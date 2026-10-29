import InitECandidate.Solver.Input.CurrentVerify.TransactionTrace
import InitECandidate.Solver.Input.VarList.RecordCells
import InitECandidate.Solver.Input.LoadWord
import InitECandidate.Solver.Input.LoopNormalExit
import InitECandidate.Solver.Input.PureGuardNormal

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original BlockErr4 guard can fall through only after reading a
nonzero length. This needs no exception-shape or successful-raise premise. -/
theorem transaction_guard_nonzero (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (read : eval source transactionLengthExpression=some (.val (.word length)))
    (normal : evaluateHOLFiniteState source emptyTransactionGuard=(none,post)) : length≠0#64 := by
  intro zero
  have observed : eval source (.cmp .equal transactionLengthExpression (.const 0#64))=some (.val (.word 1#64)):=by
    simp only [eval] at read ⊢
    simp [evalHOLExact,read,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have selected : evaluateHOLFiniteState source emptyTransactionGuard=
      evaluateHOLFiniteState source (.raise (ofString "BlockErr") (.const 4#64)):=by
    rw [emptyTransactionGuard,evaluateHOLFiniteState_ite]
    simp only [eval] at observed
    rw [observed]
    rfl
  rw [selected] at normal
  exact raise_ne_none source (ofString "BlockErr") (.const 4#64) (congrArg Prod.fst normal)

/-- A successful real scan has checked every actual row. The read premise
is only its current physical length-cell interface, transported through
this read-only loop; it assumes no later guard or trie success. -/
theorem transaction_scan_nonempty (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array : BitVec 64) (count : Nat) (lengths : Nat→BitVec 64) (small : count<2^63)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))))
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word array)))
    (readLength : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,LocalEffects.erase current=LocalEffects.erase source→
      ∀ word : BitVec 64,current.locals.lookup (ofString "i")=some (.val (.word word))→
      current.locals.lookup (ofString "txs")=some (.val (.word array))→word.toNat<count→
      eval current transactionLengthExpression=some (.val (.word (lengths word.toNat))))
    (normal : evaluateHOLFiniteState source transactionScan=(none,post)) :
    ∀ index<count,lengths index≠0#64 := by
  let invariant:=fun current : PanSemStateFiniteExact 64 Guest.HostMemory=>
    ∃ word : BitVec 64,current.locals.lookup (ofString "i")=some (.val (.word word)) ∧
      current.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))) ∧
      current.locals.lookup (ofString "txs")=some (.val (.word array)) ∧ word.toNat≤count ∧
      LocalEffects.erase current=LocalEffects.erase source ∧ ∀ index<word.toNat,lengths index≠0#64
  have initial : invariant source:=⟨0#64,counter,countCell,arrayCell,by simp,rfl,by simp⟩
  have step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code→invariant current→∀ observed : BitVec 64,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) transactionTest=some (.val (.word observed))→
      observed≠0#64→current.clock≠0→∀ target,evaluateHOLFiniteState (decClockHOLFinite current) transactionStep=(none,target)→invariant target:=by
    intro current codeEq valid observed read nonzero funded target bodyRun
    obtain ⟨word,iCell,nCell,txsCell,bound,frame,checked⟩:=valid
    have expected:=SignedGuardedCounterLoop.test_read (ofString "ntx") count small current word iCell nCell bound
    have active : word.toNat<count:=by
      by_contra inactive
      rw [if_neg inactive] at expected
      have zero : observed=0#64:=by
        simpa only [transactionTest,localVar,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using read.symm.trans expected
      exact nonzero zero
    obtain ⟨guardPost,guardRun,incrementRun⟩:=sequence_none (decClockHOLFinite current) target emptyTransactionGuard transactionIncrement bodyRun
    have last:=transaction_guard_nonzero (decClockHOLFinite current) guardPost (lengths word.toNat)
      (readLength (decClockHOLFinite current) frame word iCell txsCell active) guardRun
    have endpoint:=transaction_guarded.normal (decClockHOLFinite current) target word iCell bodyRun
    have nextNumber : (word+1#64).toNat=word.toNat+1:=by
      rw [BitVec.toNat_add_of_lt (by change word.toNat+1<2^64; omega)]
      rfl
    rw [endpoint]
    refine ⟨word+1#64,bind_lookup_same _ _ _,?_,?_,?_,frame,?_⟩
    · exact (bind_lookup_other _ "i" "ntx" _ (by decide)).trans nCell
    · exact (bind_lookup_other _ "i" "txs" _ (by decide)).trans txsCell
    · rw [nextNumber]; omega
    · intro index before
      rw [nextNumber] at before
      by_cases old : index<word.toNat
      · exact checked index old
      · have same : index=word.toNat:=by omega
        rw [same]
        exact last
  obtain ⟨word,iCell,nCell,txsCell,bound,frame,checked⟩:=loop_invariant_no_control source.code transactionTest transactionStep
    transaction_guarded.no_control invariant step source post rfl initial normal
  have exited:=loop_normal_exit transactionTest transactionStep (fun current=>(transaction_guarded.no_control current).1) source post normal
  have expected:=SignedGuardedCounterLoop.test_read (ofString "ntx") count small post word iCell nCell bound
  have finalCount : word.toNat=count:=by
    by_cases active : word.toNat<count
    · rw [if_pos active] at expected
      have impossible : (0#64 : BitVec 64)=1#64:=by
        simpa only [transactionTest,localVar,Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using exited.symm.trans expected
      exact False.elim ((by decide : (0#64 : BitVec 64)≠1#64) impossible)
    · omega
  intro index before
  exact checked index (by rw [finalCount]; exact before)

/-- Instantiate the scan's physical read interface with the actual decoded
SSZ record cells. Successful scanning therefore checks the original input's
record lengths, rather than a hypothetical next-row contract. -/
theorem transaction_records_nonempty (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (input : Guest.InputBlob) (pointer array : BitVec 64) (start size : Nat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (records : VarList.Records source input pointer array start size)
    (counter : source.locals.lookup (ofString "i")=some (.val (.word 0#64)))
    (countCell : source.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start size)))))
    (arrayCell : source.locals.lookup (ofString "txs")=some (.val (.word (VarList.decodedArray array size))))
    (normal : evaluateHOLFiniteState source transactionScan=(none,post)) :
    ∀ index<VarList.decodedCount input start size,VarList.recordLength input start size (VarList.decodedCount input start size) index≠0#64 := by
  obtain ⟨countBound,small,cells⟩:=records.cells source input pointer array start size domain
  apply transaction_scan_nonempty source post (VarList.decodedArray array size) (VarList.decodedCount input start size)
    (VarList.recordLength input start size (VarList.decodedCount input start size)) (by omega) counter countCell arrayCell _ normal
  intro current frame word iCell txsCell before
  have domainEq:=congrArg PanSemStateFiniteExact.memaddrs frame
  change current.memaddrs=source.memaddrs at domainEq
  have memoryEq:=LocalEffects.memory_of_erase source current frame
  obtain ⟨mapped,stored⟩:=cells word.toNat before
  have multiply : word*16#64=BitVec.ofNat 64 (16*word.toNat):=by
    simp [BitVec.ofNat_mul,BitVec.mul_comm]
  have addressRead : eval current (.op .add [localVar "txs",.panop .mul [localVar "i",.const 16#64],.const 8#64])=
      some (.val (.word (VarList.lengthCell (VarList.decodedArray array size) word.toNat))):=by
    simp [eval,evalHOLExact,evalListHOLExact,toExact,localVar,iCell,txsCell,valueIsWord,valueWord,panOpHOL,wordOpHOL,wordOp,
      VarList.lengthCell,VarList.row,multiply,BitVec.add_assoc]
  exact Witness.load_word_read current _ _ _ addressRead (by rw [domainEq]; exact mapped) (by rw [memoryEq]; exact stored)

/-- Pure input fact established by the original successful main scan. -/
def TransactionsNonempty (input : Guest.InputBlob) : Prop :=
  let start:=62+Guest.GasLimit.le32 input 566
  let size:=Guest.GasLimit.le32 input 570-Guest.GasLimit.le32 input 566
  ∀ index<VarList.decodedCount input start size,VarList.recordLength input start size (VarList.decodedCount input start size) index≠0#64

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_guard_nonzero
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_scan_nonempty

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.transaction_records_nonempty
