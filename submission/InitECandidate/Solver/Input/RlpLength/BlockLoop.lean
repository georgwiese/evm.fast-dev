import InitECandidate.Solver.Input.RlpLength.BlockStep

namespace InitECandidate.Solver.Input.RlpLength.Block
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Exact actual withdrawal length accumulation. The mathematical sum stays
between25*N and57*N and fits64 bits; source modular addition never hides an
oversized withdrawal list. Every real size call and while tick is included. -/
theorem loop_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer payload : BitVec 64)
    (start index rounds count sum : Nat) (finish : index+rounds=count) (countSmall : count<2^31)
    (sumLower : 25*index≤sum) (sumUpper : sum≤57*index)
    (heap : Blob.HeapInput source input pointer) (inside : start+44*count≤input.length%2^64)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word payload)))
    (i : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index))))
    (n : source.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))))
    (wl : source.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 sum))))
    (mapped : source.memaddrs (payload+48#64)) (stored : source.memory (payload+48#64)=.word (pointer+BitVec.ofNat 64 start))
    (code : source.code.lookup (ofString "withdrawal_rlp_len")=some (Withdrawal.formals,Withdrawal.body,.one))
    (wordCode : source.code.lookup (ofString "rlp_word_encoded_len")=some (WordSize.formals,WordSize.body,.one))
    (listCode : source.code.lookup (ofString "rlp_list_header_len")=some (ListHeader.formals,ListHeader.body,.one))
    (headerCode : source.code.lookup (ofString "rlp_header_len")=some (Header.formals,Header.body,.one))
    (beCode : source.code.lookup (ofString "rlp_be_len")=some (Be.formals,Be.body,.one)) (enough : 43*rounds≤source.clock) :
    ∃ target paid finalSum,paid≤43*rounds ∧ evaluateHOLFiniteState source withdrawalLoop=(none,target) ∧
      target={source with locals:=target.locals,clock:=source.clock-paid} ∧
      target.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      target.locals.lookup (ofString "wl")=some (.val (.word (BitVec.ofNat 64 finalSum))) ∧
      25*count≤finalSum ∧ finalSum≤57*count ∧ (BitVec.ofNat 64 finalSum).toNat=finalSum ∧
      (∀ name : String,ofString "wl"≠ofString name→ ofString "i"≠ofString name→target.locals.lookup (ofString name)=source.locals.lookup (ofString name)) := by
  classical
  induction rounds generalizing source index sum with
  | zero=>
    have inactive : ¬index<count := by omega
    have test:=test_read source index count (by omega) (by omega) i n
    simp only [if_neg inactive] at test
    have bridge : evalHOLFinite source loopTest=eval source loopTest :=
      congrArg (fun h : DecidablePred source.memaddrs=>@evalHOLExact 64 Guest.HostMemory _ source.toExact h loopTest) (Subsingleton.elim _ _)
    have finiteTest:=bridge.trans test
    have same : index=count := by omega
    refine ⟨source,0,sum,by omega,?_,by simp,?_,wl,by omega,by omega,?_,by intros; rfl⟩
    · rw [loop_shape,evaluateHOLFiniteState_while_total,finiteTest]
      simp
    · simpa only [same] using i
    · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  | succ rounds ih=>
    have active : index<count := by omega
    have test:=test_read source index count (by omega) (by omega) i n
    simp only [if_pos active] at test
    let entry:=decClockHOLFinite source
    have entryHeap : Blob.HeapInput entry input pointer:=Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
    obtain ⟨encoded,bodyPaid,encodedLower,encodedUpper,bodyBound,bodyRun⟩:=body_execute entry input pointer payload start index sum entryHeap (by omega)
      pl i wl mapped stored code wordCode listCode headerCode beCode (by change 42≤source.clock-1; omega)
    let next:=step entry bodyPaid index sum encoded
    have nextState : next={entry with locals:=next.locals,clock:=entry.clock-1-bodyPaid}:=step_state entry bodyPaid index sum encoded
    have nextClock:=congrArg PanSemStateFiniteExact.clock nextState
    change next.clock=source.clock-1-1-bodyPaid at nextClock
    have fields:=step_fields entry bodyPaid index sum encoded
    have nextPL : next.locals.lookup (ofString "pl")=some (.val (.word payload)) :=
      (step_other entry bodyPaid index sum encoded "pl" (by decide) (by decide)).trans pl
    have nextN : next.locals.lookup (ofString "nwd")=some (.val (.word (BitVec.ofNat 64 count))) :=
      (step_other entry bodyPaid index sum encoded "nwd" (by decide) (by decide)).trans n
    have nextHeap : Blob.HeapInput next input pointer:=Blob.HeapInput.of_fields source next input pointer rfl rfl rfl heap
    obtain ⟨target,tailPaid,finalSum,bound,tailRun,targetState,finalI,finalWL,lower,upper,number,others⟩:=ih next (index+1) (sum+encoded)
      (by omega) (by omega) (by omega) nextHeap nextPL fields.1 nextN fields.2 mapped stored code wordCode listCode headerCode beCode (by omega)
    have resumed:=while_active source next loopTest loopBody none test (by omega) bodyRun (by omega)
    have actual : evaluateHOLFiniteState source withdrawalLoop=(none,target) := by
      rw [loop_shape] at tailRun ⊢
      exact resumed.trans tailRun
    refine ⟨target,bodyPaid+tailPaid+2,finalSum,by omega,actual,?_,finalI,finalWL,lower,upper,number,?_⟩
    · rw [nextState] at targetState
      change target={source with locals:=target.locals,clock:=source.clock-1-1-bodyPaid-tailPaid} at targetState
      have subtract : source.clock-1-1-bodyPaid-tailPaid=source.clock-(bodyPaid+tailPaid+2) := by omega
      simpa only [subtract] using targetState
    · intro name wlNe iNe
      exact (others name wlNe iNe).trans (step_other entry bodyPaid index sum encoded name wlNe iNe)

end InitECandidate.Solver.Input.RlpLength.Block

#print axioms InitECandidate.Solver.Input.RlpLength.Block.loop_execute
