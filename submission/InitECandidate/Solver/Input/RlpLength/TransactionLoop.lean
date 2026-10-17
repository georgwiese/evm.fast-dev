import InitECandidate.Solver.Input.RlpLength.TransactionStep

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def TxRecords (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (lengths pointers : Nat→BitVec 64) (bytes : Nat→UInt8) (count : Nat) : Prop :=
  ∀ index<count,source.memaddrs (VarList.lengthCell array index) ∧ source.memory (VarList.lengthCell array index)=.word (lengths index) ∧
    source.memaddrs (VarList.row array index) ∧ source.memory (VarList.row array index)=.word (pointers index) ∧
    (lengths index≠0#64→ @panMemLoadByteHOL 64 _ source.memory source.memaddrs (fun address=>Classical.propDecidable (source.memaddrs address)) source.be (pointers index)=some (bytes index))

theorem tx_test_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index count : Nat)
    (indexSmall : index<2^63) (countSmall : count<2^63)
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count)))) :
    eval source txTest=some (.val (.word (if index<count then 1#64 else 0#64))) := by
  classical
  have indexSign : index<9223372036854775808:=indexSmall
  have countSign : count<9223372036854775808:=countSmall
  have ie : (BitVec.ofNat 64 index).toNat=index := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have ce : (BitVec.ofNat 64 count).toNat=count := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  simp [eval,txTest,localVar,evalHOLExact,toExact,i,n,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,BitVec.lt_def,ie,ce,indexSign,countSign]

theorem tx_step_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (paid index sum encoded : Nat) (name : String)
    (tlNe : ofString "tl"≠ofString name) (iNe : ofString "i"≠ofString name) :
    (txStep source paid index sum encoded).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "i" name _ iNe).trans (bind_lookup_other _ "tl" name _ tlNe)

/-- Actual complete transaction accumulation loop. The decoded raw-byte total
is charged once; each record adds at most nine RLP overhead bytes. -/
theorem tx_loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array : BitVec 64)
    (lengths pointers : Nat→BitVec 64) (bytes : Nat→UInt8) (index rounds count sum : Nat)
    (finish : index+rounds=count) (countSmall : count<2^31)
    (sizes : ∀ position<count,(lengths position).toNat≤134217712)
    (totals : ∀ position≤count,VarList.sumPrefix (fun j=>(lengths j).toNat) position≤134217712)
    (sumUpper : sum≤VarList.sumPrefix (fun j=>(lengths j).toNat) index+9*index)
    (records : TxRecords source array lengths pointers bytes count)
    (txs : source.locals.lookup (ofString "txs")=some (.val (.word array)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))))
    (tl : source.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (code : source.code.lookup (ofString "rlp_bytes_encoded_len")=some (BytesSize.formals,BytesSize.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 12*rounds≤source.clock) :
    ∃ target paid finalSum,paid≤12*rounds ∧ evaluateHOLFiniteState source transactionLoop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      target.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 finalSum))) ∧
      finalSum≤VarList.sumPrefix (fun j=>(lengths j).toNat) count+9*count ∧ (BitVec.ofNat 64 finalSum).toNat=finalSum ∧
      (∀ name : String,ofString "tl"≠ofString name→ ofString "i"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) := by
  classical
  induction rounds generalizing source index sum with
  | zero=>
    have inactive : ¬index<count := by omega
    have test:=tx_test_read source index count (by omega) (by omega) i n
    simp only [if_neg inactive] at test
    have bridge : evalHOLFinite source txTest=eval source txTest :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h txTest) (Subsingleton.elim _ _)
    have finiteTest:=bridge.trans test
    have same : index=count := by omega
    have totalBound:=totals count (Nat.le_refl _)
    refine ⟨source,0,sum,by omega,?_,by simp,?_,tl,by simpa only [same] using sumUpper,?_,by intros; rfl⟩
    · rw [transaction_loop_shape,evaluateHOLFiniteState_while_total,finiteTest]
      simp
    · simpa only [same] using i
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by rw [same] at sumUpper; omega)]
  | succ rounds ih=>
    have active : index<count := by omega
    have test:=tx_test_read source index count (by omega) (by omega) i n
    simp only [if_pos active] at test
    let entry:=decClockHOLFinite source
    obtain ⟨lengthMapped,lengthStored,pointerMapped,pointerStored,loaded⟩:=records index active
    obtain ⟨encoded,bodyPaid,lower,upper,bodyBound,bodyRun⟩:=tx_body_execute entry array (pointers index) (lengths index) (bytes index) index sum
      (sizes index active) txs i tl lengthMapped lengthStored pointerMapped pointerStored loaded code headerCode beCode (by change 11≤source.clock-1; omega)
    let next:=txStep entry bodyPaid index sum encoded
    have nextState : next={entry with locals:=next.locals,clock:=entry.clock-bodyPaid}:=rfl
    have nextClock:=congrArg PanSemStateFiniteExact.clock nextState
    change next.clock=source.clock-1-bodyPaid at nextClock
    have nextTxs : next.locals.lookup (ofString "txs")=some (.val (.word array)) :=
      (tx_step_other entry bodyPaid index sum encoded "txs" (by decide) (by decide)).trans txs
    have nextN : next.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))) :=
      (tx_step_other entry bodyPaid index sum encoded "ntx" (by decide) (by decide)).trans n
    have nextI : next.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index+1)))):=bind_lookup_same _ _ _
    have nextTL : next.locals.lookup (ofString "tl")=some (.val (.word (BitVec.ofNat 64 (sum+encoded)))) :=
      (bind_lookup_other _ "i" "tl" _ (by decide)).trans (bind_lookup_same _ _ _)
    have nextBound : sum+encoded≤VarList.sumPrefix (fun j=>(lengths j).toNat) (index+1)+9*(index+1) := by
      simp only [VarList.sumPrefix]
      omega
    obtain ⟨target,tailPaid,finalSum,bound,tailRun,targetState,finalI,finalTL,totalUpper,number,others⟩:=
      ih next (index+1) (sum+encoded) (by omega) nextBound records nextTxs nextI nextN nextTL code headerCode beCode (by omega)
    have resumed:=while_active source next txTest txBody none test (by omega) bodyRun (by omega)
    have actual : evaluateHOLFiniteState source transactionLoop=(none,target) := by
      rw [transaction_loop_shape] at tailRun ⊢
      exact resumed.trans tailRun
    refine ⟨target,bodyPaid+tailPaid+1,finalSum,by omega,actual,?_,finalI,finalTL,totalUpper,number,?_⟩
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,clock:=source.clock-1-bodyPaid-tailPaid} at targetState
      have subtract : source.clock-1-bodyPaid-tailPaid=source.clock-(bodyPaid+tailPaid+1) := by omega
      simpa only [subtract] using targetState
    · intro name tlNe iNe
      exact (others name tlNe iNe).trans (tx_step_other entry bodyPaid index sum encoded name tlNe iNe)

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_loop_execute
#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_test_read
#print axioms InitECandidate.Solver.Input.RlpLength.Block.tx_step_other
