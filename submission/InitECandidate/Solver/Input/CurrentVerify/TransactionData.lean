import InitECandidate.Solver.Input.CurrentVerify.TransactionTrace
import InitECandidate.Solver.Input.CurrentVerify.StateReturnedData
import InitECandidate.Solver.Input.LoadWord

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The real transaction pointer/count loads come from the same decoded
payload image retained through state_init. Failed record reads and empty
transactions remain covered by the original scan's all-outcome bound. -/
theorem after_state_init_transaction_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (payloadLocal : source.locals.lookup (ofString "pl")=some (.val (.word record)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterStateInit=(outcome,post)) :
    source.clock-post.clock≤12582752 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤12582752 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) := by
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
  · obtain ⟨current,inner,frame,locals,forward,price,endpoint,continued⟩:=reached
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
    exact Or.inr ⟨current,inner,data.of_frame frame currentSi,currentPayload,forward,by omega,endpoint,continued⟩

/-- Whole real main prefix through transaction scanning: the same actual
payload/header/gas/database/state-init run either stops within its allowance
or reaches payload_header with all decoded input data retained. -/
theorem to_after_transaction_scan {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤3387552531 ∨ ∃ current inner,
      Data input current pointer si record gasWord boundary ∧ current.locals.lookup (ofString "pl")=some (.val (.word record)) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤3387552531 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current afterTransactionScan=(outcome,inner) := by
  rcases to_after_state_init_with_data data outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨caller,target,inner,tables,returned,currentData,forward,price,continued,endpoint,physical⟩:=reached
    rcases after_state_init_transaction_trace currentData tables.2.1 outcome continued with stopped|reached
    · change target.clock-inner.clock≤12582752 at stopped
      exact Or.inl (by rw [endpoint]; omega)
    · obtain ⟨current,last,lastData,payloadLocal,scanForward,scanPrice,scanClock,lastRun⟩:=reached
      change current.clock≤target.clock at scanForward
      change target.clock-current.clock≤12582752 at scanPrice
      exact Or.inr ⟨current,last,lastData,payloadLocal,by change current.clock≤source.clock; omega,
        by change source.clock-current.clock≤3387552531; omega,endpoint.trans scanClock,lastRun⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.after_state_init_transaction_trace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_transaction_scan
