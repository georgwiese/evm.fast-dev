import InitECandidate.Solver.Input.RlpLength.BlockReads

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem body_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer payload : BitVec 64)
    (start index sum : Nat) (heap : Blob.HeapInput source input pointer) (inside : start+44*index+44≤input.length%2^64)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (wl : source.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 start))
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 42≤source.clock) :
    ∃ encoded paid,25≤encoded ∧ encoded≤57 ∧ paid≤41 ∧
      evaluateHOLFiniteState source loopBody=(none,step source paid index sum encoded) := by
  classical
  have args:=arguments_read source pointer payload start index pl i mapped stored
  obtain ⟨encoded,paid,lower,upper,bound,called⟩:=Withdrawal.call_execute source input pointer (start+44*index) heap (by omega)
    "wlen" withdrawalArguments afterLength args code wordCode listCode headerCode beCode enough
  let entered:=bind {source with clock:=source.clock-1-paid} "wlen" (BitVec.ofNat 64 encoded)
  have enteredWL : entered.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 sum))) :=
    (bind_lookup_other _ "wlen" "wl" _ (by decide)).trans wl
  have enteredI : entered.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other _ "wlen" "i" _ (by decide)).trans i
  have enteredLength : entered.locals.lookup (ofString "wlen")=some (.val (.word (BitVec.ofNat 64 encoded))):=bind_lookup_same _ _ _
  have readSum : eval entered sumExpression=some (.val (.word (BitVec.ofNat 64 (sum+encoded)))) := by
    simp [eval,sumExpression,localVar,evalHOLExact,evalListHOLExact,toExact,enteredWL,enteredLength,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  have runSum:=WitnessRadix.StateSteps.assign_execute entered "wl" sumExpression _ _ enteredWL readSum
  let added:=bind entered "wl" (BitVec.ofNat 64 (sum+encoded))
  have addedI : added.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))) :=
    (bind_lookup_other entered "wl" "i" _ (by decide)).trans enteredI
  have readI : eval added incrementExpression=some (.val (.word (BitVec.ofNat 64 (index+1)))) := by
    simp [eval,incrementExpression,localVar,evalHOLExact,evalListHOLExact,toExact,addedI,valueIsWord,valueWord,wordOpHOL,wordOp,←BitVec.ofNat_add]
  have runI:=WitnessRadix.StateSteps.assign_execute added "i" incrementExpression _ _ addedI readI
  have tailRun : evaluateHOLFiniteState entered afterLength=(none,bind added "i" (BitVec.ofNat 64 (index+1))) := by
    rw [afterLength,WitnessRadix.StateSteps.next_sequence entered added _ _ runSum (Nat.le_refl _)]
    exact runI
  have restored : restore source "wlen" (bind added "i" (BitVec.ofNat 64 (index+1)))=step source paid index sum encoded := by
    rw [restore_bind_other source added "wlen" "i" _ (by decide)]
    change bind (restore source "wlen" (bind entered "wl" (BitVec.ofNat 64 (sum+encoded)))) "i" _=_
    rw [restore_bind_other source entered "wlen" "wl" _ (by decide)]
    have temporary : restore source "wlen" entered={source with clock:=source.clock-1-paid}:=
      restore_bound {source with clock:=source.clock-1-paid} "wlen" (BitVec.ofNat 64 encoded)
    rw [temporary]
    rfl
  refine ⟨encoded,paid,lower,upper,bound,?_⟩
  rw [loopBody,called,tailRun]
  exact congrArg (fun target : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,target)) restored

theorem step_state (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) :
    step source paid index sum encoded={source with locals:=(step source paid index sum encoded).locals,clock:=source.clock-1-paid} := rfl

theorem step_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) :
    (step source paid index sum encoded).locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))) ∧
    (step source paid index sum encoded).locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 (sum+encoded)))) :=
  ⟨bind_lookup_same _ _ _,(bind_lookup_other _ "i" "wl" _ (by decide)).trans (bind_lookup_same _ _ _)⟩

theorem step_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) (name : String)
    (wlNe : ofString "wl"≠ofString name) (iNe : ofString "i"≠ofString name) :
    (step source paid index sum encoded).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "i" name _ iNe).trans (bind_lookup_other _ "wl" name _ wlNe)

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.body_execute
#print axioms InitECandidate.Solver.Input.RlpLength.Block.step_other
