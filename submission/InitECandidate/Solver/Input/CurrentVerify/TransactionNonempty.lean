import InitECandidate.Solver.Input.CurrentVerify.TransactionTrace
import InitECandidate.Solver.Input.CurrentVerify.StateReturnedData
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


namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real transaction pointer/count loads come from the same decoded
payload image retained through state_init. Failed record reads and empty
transactions remain covered by the original scan's all-outcome bound. -/
theorem after_state_init_transaction_frame_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payloadLocal : source.locals.lookup (ofString "pl")=some (.val (.word record)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterStateInit=(outcome,post)) :
    source.clock-post.clock≤12582752 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤12582752 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input ∧
      LocalEffects.erase current=LocalEffects.erase source := by
  obtain ⟨array,length,start,size,payload,arrayBefore,countBound,byteBound⟩:=data.payload
  let count:=VarList.decodedCount input start size
  let actualArray:=VarList.decodedArray array size
  have localRead : eval source (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,localVar,toExact,payloadLocal]
  have arrayRead : eval source transactionArrayExpression=some (.val (.word actualArray)):=
    Witness.load_word_read source (Scalar.plus (localVar "pl") 32) (record+32#64) actualArray
      (Scalar.plus_read source (localVar "pl") record 32 localRead)
      (AllocatedBytes.word_mapped source record 136 32 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.txs
  let next:=bind source "txs" actualArray
  have nextPayload : next.locals.lookup (ofString "pl")=some (.val (.word record)):=
    (bind_lookup_other source "txs" "pl" actualArray (by decide)).trans payloadLocal
  have nextLocal : eval next (localVar "pl")=some (.val (.word record)):=by simp [eval,evalHOLExact,localVar,toExact,nextPayload]
  have countRead : eval next transactionCountExpression=some (.val (.word (BitVec.ofNat 64 count))):=
    Witness.load_word_read next (Scalar.plus (localVar "pl") 40) (record+40#64) (BitVec.ofNat 64 count)
      (Scalar.plus_read next (localVar "pl") record 40 nextLocal)
      (AllocatedBytes.word_mapped next record 136 40 data.arena.domain data.recordArena (by decide) data.recordAligned (by decide)) payload.transactions.count
  rcases transaction_prefix_trace source post actualArray count (by dsimp [count]; omega) arrayRead countRead outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨current,inner,frame,locals,forward,price,endpoint,continued,scanRun⟩:=reached
    have entrySi : (transactionScanEntry source actualArray count).locals.lookup (ofString "si")=source.locals.lookup (ofString "si"):=
      (bind_lookup_other _ "i" "si" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "si" (BitVec.ofNat 64 count) (by decide)).trans
          (bind_lookup_other source "txs" "si" actualArray (by decide)))
    have entryPayload : (transactionScanEntry source actualArray count).locals.lookup (ofString "pl")=source.locals.lookup (ofString "pl"):=
      (bind_lookup_other _ "i" "pl" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "pl" (BitVec.ofNat 64 count) (by decide)).trans
          (bind_lookup_other source "txs" "pl" actualArray (by decide)))
    have currentSi : current.locals.lookup (ofString "si")=some (.val (.word si)):=
      (locals _ (by decide)).trans (entrySi.trans data.siLocal)
    have currentPayload : current.locals.lookup (ofString "pl")=some (.val (.word record)):=
      (locals _ (by decide)).trans (entryPayload.trans payloadLocal)
    let scanEntry:=transactionScanEntry source actualArray count
    have scanRecords : VarList.Records scanEntry input pointer array start size:=
      VarList.Records.of_memory source scanEntry input pointer array start size rfl payload.transactions.records
    have scanCounter : scanEntry.locals.lookup (ofString "i")=some (.val (.word 0#64)):=bind_lookup_same _ _ _
    have scanCount : scanEntry.locals.lookup (ofString "ntx")=some (.val (.word (BitVec.ofNat 64 count))):=
      (bind_lookup_other _ "i" "ntx" 0#64 (by decide)).trans (bind_lookup_same _ _ _)
    have scanArray : scanEntry.locals.lookup (ofString "txs")=some (.val (.word actualArray)):=
      (bind_lookup_other _ "i" "txs" 0#64 (by decide)).trans
        ((bind_lookup_other _ "ntx" "txs" (BitVec.ofNat 64 count) (by decide)).trans (bind_lookup_same _ _ _))
    have nonempty:=transaction_records_nonempty scanEntry current input pointer array start size data.arena.domain scanRecords scanCounter scanCount scanArray scanRun
    have checked : TransactionsNonempty input:=by
      unfold TransactionsNonempty
      rw [←payload.transactions.startEq,←payload.transactions.sizeEq]
      exact nonempty
    exact Or.inr ⟨current,inner,data.of_frame frame currentSi,currentPayload,forward,by omega,endpoint,continued,checked,frame⟩

/-- Existing consumers retain the original projection; the stronger trace
also exposes the complete nonlocal equality of the transaction scan. -/
theorem after_state_init_transaction_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payloadLocal : source.locals.lookup (ofString "pl")=some (.val (.word record)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterStateInit=(outcome,post)) :
    source.clock-post.clock≤12582752 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤12582752 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input := by
  rcases after_state_init_transaction_frame_trace data payloadLocal outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨current,inner,physical,payload,forward,price,clock,continued,checked,frame⟩:=reached
    exact Or.inr ⟨current,inner,physical,payload,forward,price,clock,continued,checked⟩

/-- Whole real main prefix through transaction scanning: the same actual
payload/header/gas/database/state-init run either stops within its allowance
or reaches payload_header with all decoded input data retained. -/
theorem to_after_transaction_scan {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1760814515536 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1760814515536 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input := by
  rcases to_after_state_init_with_data data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,target,inner,tables,returned,currentData,forward,price,continued,endpoint,physical⟩:=reached
    rcases after_state_init_transaction_trace currentData tables.2.1 outcome continued with stopped|reached
    · change target.clock-inner.clock≤12582752 at stopped
      exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,last,lastData,payloadLocal,scanForward,scanPrice,scanClock,lastRun,checked⟩:=reached
      change current.clock≤target.clock at scanForward
      change target.clock-current.clock≤12582752 at scanPrice
      exact Or.inr ⟨current,last,lastData,payloadLocal,by change current.clock≤source.clock; omega,
        by change source.clock-current.clock≤1760814515536; omega,endpoint.trans scanClock,lastRun,checked⟩

/-- Main's original payload_header entry now retains the actual initialized
records and the pre-workspace witness-memory frame, as well as decoded input. -/
theorem to_after_transaction_scan_with_records {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1760814515536 ∨ ∃ caller current inner ws bs,
      HasTables input caller pointer si record gasWord boundary ∧
      caller.globals.lookup (ofString "heap_ptr")=some (.val (.word ws)) ∧
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      Mpt.StateInit.MemoryContext current ws ws bs ∧ Mpt.WitnessCore.Stack.StablePrefix caller current ws.toNat ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤1760814515536 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) ∧ TransactionsNonempty input := by
  rcases to_after_state_init_with_records data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,target,inner,ws,bs,tables,returned,currentData,cell,records,recordFrame,forward,price,continued,endpoint,physical⟩:=reached
    rcases after_state_init_transaction_frame_trace currentData tables.2.1 outcome continued with stopped|reached
    · change target.clock-inner.clock≤12582752 at stopped
      exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,last,lastData,payload,scanForward,scanPrice,scanClock,lastRun,checked,scanFrame⟩:=reached
      change current.clock≤target.clock at scanForward
      change target.clock-current.clock≤12582752 at scanPrice
      exact Or.inr ⟨caller,current,last,ws,bs,tables,cell,lastData,payload,records.of_frame scanFrame,
        (by intro query earlier
            exact (congrFun (LocalEffects.memory_of_erase {target with locals:=caller.locals} current scanFrame) query).trans (recordFrame query earlier)),
        by omega,by omega,endpoint.trans scanClock,lastRun,checked⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_transaction_frame_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_transaction_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_transaction_scan
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_transaction_scan_with_records
