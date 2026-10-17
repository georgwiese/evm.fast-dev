import InitECandidate.Solver.Input.RlpLength.TransactionReads

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- One actual transaction-length loop body, including the conditional first
byte read, legacy/raw branch, typed wrapping call and all local scopes. -/
theorem tx_body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer n : BitVec 64) (byte : UInt8) (index sum : Nat)
    (small : n.toNat≤134217712)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (lengthMapped : source.memaddrs (VarList.lengthCell array index)) (lengthStored : source.memory (VarList.lengthCell array index)=.word n)
    (pointerMapped : source.memaddrs (VarList.row array index)) (pointerStored : source.memory (VarList.row array index)=.word pointer)
    (loaded : n≠0#64→ @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be pointer=some byte)
    (code : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 11≤source.clock) :
    ∃ encoded paid,n.toNat≤encoded ∧ encoded≤n.toNat+9 ∧ paid≤11 ∧
      evaluateHOLFiniteState source txBody=(none,txStep source paid index sum encoded) := by
  classical
  let sn:=bind source "n" n
  let sf:=bind sn "fb" 0#64
  let first:=if n=0#64 then 0#64 else BitVec.ofNat 64 byte.toNat
  let entered:=bind sn "fb" first
  have nSF : sf.locals.lookup (ofString "n")=some (.val (.word n)) :=
    (bind_lookup_other _ "fb" "n" _ (by decide)).trans (bind_lookup_same _ _ _)
  have fbSF : sf.locals.lookup (ofString "fb")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
  have firstRun : evaluateHOLFiniteState sf txReadFirst=(none,entered) := by
    have test : eval sf (.cmp .notEqual (localVar "n") (.const 0#64))=some (.val (.word (if n=0#64 then 0#64 else 1#64))) := by
      simp [eval,localVar,evalHOLExact,toExact,nSF,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp only [eval] at test
    rw [txReadFirst,evaluateHOLFiniteState_ite,test]
    by_cases zero : n=0#64
    · simp [zero,entered,first,sf]
    · have txsSF : sf.locals.lookup (ofString "txs")=some (.val (.word array)) :=
        (bind_lookup_other _ "fb" "txs" _ (by decide)).trans ((bind_lookup_other _ "n" "txs" _ (by decide)).trans txs)
      have iSF : sf.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
        (bind_lookup_other _ "fb" "i" _ (by decide)).trans ((bind_lookup_other _ "n" "i" _ (by decide)).trans i)
      have read:=tx_first_read sf array pointer index byte txsSF iSF pointerMapped pointerStored (loaded zero)
      have assigned:=WitnessRadix.StateSteps.assign_execute sf "fb" txFirstExpression _ _ fbSF read
      simp only [if_neg zero]
      simpa [entered,first,zero,sf,bind_twice] using assigned
  have nEntered : entered.locals.lookup (ofString "n")=some (.val (.word n)) :=
    (bind_lookup_other _ "fb" "n" _ (by decide)).trans (bind_lookup_same _ _ _)
  have fbEntered : entered.locals.lookup (ofString "fb")=some (.val (.word first)):=bind_lookup_same _ _ _
  have iEntered : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other _ "fb" "i" _ (by decide)).trans ((bind_lookup_other _ "n" "i" _ (by decide)).trans i)
  have tlEntered : entered.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 sum))) :=
    (bind_lookup_other _ "fb" "tl" _ (by decide)).trans ((bind_lookup_other _ "n" "tl" _ (by decide)).trans tl)
  obtain ⟨encoded,paid,lower,upper,bound,tailRun⟩:=tx_after_first_execute entered first n index sum small fbEntered nEntered iEntered tlEntered code headerCode beCode enough
  have sequenceRun : evaluateHOLFiniteState sf (.seq txReadFirst txAfterFirst)=(none,txStep entered paid index sum encoded) := by
    rw [WitnessRadix.StateSteps.next_sequence sf entered _ _ firstRun (Nat.le_refl _)]
    exact tailRun
  have fbRead : eval sn (.const 0#64)=some (.val (.word 0#64)):=rfl
  have fbDeclared:=ScalarScope.declare_execute sn _ "fb" (.const 0#64) 0#64 (.seq txReadFirst txAfterFirst) none fbRead sequenceRun
  have lengthRead:=tx_length_read source array n index txs i lengthMapped lengthStored
  have nDeclared:=ScalarScope.declare_execute source _ "n" txLengthExpression n txAfterLength none lengthRead fbDeclared
  refine ⟨encoded,paid,lower,upper,bound,?_⟩
  change evaluateHOLFiniteState source (.dec (ofString "n") .one txLengthExpression txAfterLength)=_
  rw [nDeclared,tx_step_restore sn entered "fb" paid index sum encoded (by decide) (by decide),restore_bound,
    tx_step_restore source sn "n" paid index sum encoded (by decide) (by decide),restore_bound]

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_body_execute
