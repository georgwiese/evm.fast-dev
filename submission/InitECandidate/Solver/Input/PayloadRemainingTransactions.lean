import InitECandidate.Solver.Input.PayloadRemainingProgram
import InitECandidate.Solver.Input.PayloadFieldsFrame
import InitECandidate.Solver.Input.PayloadTransactionImage
import InitECandidate.Solver.Input.PayloadPrefixFields

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The literal eleven final payload stores retain the complete transaction
image. In particular no gas/withdrawal/balance write reaches its record array. -/
theorem TransactionImage.after_remaining {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {start size : Nat}
    (data : TransactionImage input source pointer record array start size)
    (length withdrawals balances count : BitVec 64) (room : record.toNat + 136 ≤ 33806089496) :
    TransactionImage input
      (emptyLocalsHOLFinite (applyFields source record (remainingFields input pointer length withdrawals balances count)))
      pointer record array start size := by
  let fields := remainingFields input pointer length withdrawals balances count
  have valid : ∀ field ∈ fields, field.1 ≤ 128 :=
    fun field member => (remaining_valid input pointer length withdrawals balances count field member).1
  have records := applyFields_records source input pointer record array start size fields data.records data.arrayAfter room valid
  refine ⟨data.startEq, data.sizeEq, data.inside, data.arrayAfter, data.heapExtent,
    VarList.Records.of_memory (applyFields source record fields) _ input pointer array start size rfl records, ?_, ?_, ?_⟩
  · have frame : (applyFields source record fields).memory (record + 32#64) = source.memory (record + 32#64) := by
      simpa [cellValue, fields, remainingFields] using applyFields_cell source record room fields valid 32 (by decide)
    exact frame.trans data.txs
  · have frame : (applyFields source record fields).memory (record + 40#64) = source.memory (record + 40#64) := by
      simpa [cellValue, fields, remainingFields] using applyFields_cell source record room fields valid 40 (by decide)
    exact frame.trans data.count

  · have later : ∀ field ∈ fields, 32 ≤ field.1 ∧ field.1 ≤ 128 := by
      intro field member
      simp only [fields, remainingFields, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [Prod.fst] <;> decide
    exact (data.hashPrefix.fields_after fields room later).of_frame rfl

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.TransactionImage.after_remaining
