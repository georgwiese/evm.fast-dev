import InitECandidate.Solver.Input.CurrentStartup.TransactionEntry
import InitECandidate.Solver.Input.VarList.NormalEntry
import InitECandidate.Solver.Input.VarList.EncodedCount

namespace InitECandidate.Solver.Input.CurrentStartup.VarListRoom
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actually returned current list is empty, or its real allocator must
have room for16*count. Clock padding only funds guard inversion; all size/room
conclusions refer to the original state and raw input. -/
theorem returned_room (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64) (start length floor : Nat) (installed : OriginalCode.Installed source.code)
    (shapes : OriginalExceptions.Installed source.eshapes) (heap : NormalHeapEffects.AtLeast floor source)
    (image : Blob.HeapInput source input pointer) (inside : start + length ≤ input.length % 2^64)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source VarList.body = (some (.returned value), post)) :
    (length = 0 ∧ value = VarList.emptyValue) ∨
      (∃ array : BitVec 64, source.globals.lookup (ofString "heap_ptr") = some (.val (.word array)) ∧
        floor ≤ array.toNat ∧ array.toNat % 8 = 0 ∧ 4 ≤ length ∧
        0 < Guest.GasLimit.le32 input start / 4 ∧
        4 * (Guest.GasLimit.le32 input start / 4) = Guest.GasLimit.le32 input start ∧
        Guest.GasLimit.le32 input start ≤ length ∧ Guest.GasLimit.le32 input start / 4 ≤ limit.toNat ∧
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) := by
  let padded : PanSemStateFiniteExact 64 Guest.HostMemory := {source with clock := source.clock + 1}
  have paddedRun := panPropsEvaluateAddClockEq VarList.body source (some (.returned value)) post 1 ⟨actual, by simp⟩
  rcases VarList.normal_entry padded {post with clock := post.clock + 1} input pointer limit start length image inside p n l
    (CanonicalHeader.fail_code source.code installed) (shapes .SszErr) (by dsimp [padded]; omega) value paddedRun with empty | parsed
  · exact Or.inl empty
  · obtain ⟨minimum, countPositive, header, firstUpper, countBound, inner, allocationRun, restored⟩ := parsed
    obtain ⟨array, heapCell, low, arrayBound, aligned⟩ := heap
    let count := Guest.GasLimit.le32 input start / 4
    let first := BitVec.ofNat 64 (Guest.GasLimit.le32 input start)
    let entered := bind padded "first" first
    let ready := VarList.counted entered first
    let amount := BitVec.ofNat 64 (16 * count)
    have countLocal : ready.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))) := by
      have encoded : VarList.countWord first = BitVec.ofNat 64 count := VarList.count_encode input start
      exact (bind_lookup_same entered "count" (VarList.countWord first)).trans
        (congrArg (fun word : BitVec 64 => some (ValueHOL.val (HolWordLab.word word))) encoded)
    have amountNat : amount.toNat = 16 * count := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Framing.le32_lt input start; dsimp [count]; omega)]
    have read : eval ready VarList.allocationExpression = some (.val (.word amount)) := by
      have actual := VarList.allocation_read ready (BitVec.ofNat 64 count) countLocal
      simpa only [← BitVec.ofNat_mul, Nat.mul_comm count 16] using actual
    have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) [VarList.allocationExpression] =
        some (WitnessRadix.PersistentAlloc.values amount) := by
      simp only [eval] at read
      simp [evalListHOLFinite, evalListHOLExact, read, WitnessRadix.PersistentAlloc.values]
    obtain ⟨room, positive, after, remaining, frame⟩ := WitnessRadix.PersistentAlloc.call_normal ready inner "arr" [VarList.allocationExpression]
      VarList.allocatedTail array amount args (allocation_entry source.code installed) (trap_entry source.code installed) heapCell arrayBound value allocationRun
    rw [amountNat] at room
    exact Or.inr ⟨array, heapCell, low, aligned, minimum, countPositive, header, firstUpper, countBound, room⟩

/-- Apply allocation inversion at the genuine main-derived transaction
callee. Nonempty room is bounded by the real current allocator ceiling. -/
theorem transaction (input : Guest.InputBlob) (actual : TransactionEntry.Reached input) :
    ∃ record : BitVec 64, ∃ start length : Nat,
      start = 62 + Guest.GasLimit.le32 input 566 ∧ length = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566 ∧
      ((length = 0) ∨ ∃ array : BitVec 64,
        record.toNat + 136 ≤ array.toNat ∧ array.toNat % 8 = 0 ∧
        0 < Guest.GasLimit.le32 input start / 4 ∧
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) := by
  obtain ⟨caller, entry, post, pointer, record, size, start, length, value, context, installed, shapes, domain, endian,
    globals, image, heap, p, n, l, startEq, lengthEq, inside, returned⟩ := actual
  rcases returned_room input entry post pointer 9223372036854775807#64 start length (record.toNat + 136)
    installed shapes heap image inside p n l value returned with empty | allocated
  · exact ⟨record, start, length, startEq, lengthEq, Or.inl empty.1⟩
  · obtain ⟨array, cell, low, aligned, minimum, positive, header, upper, limit, room⟩ := allocated
    exact ⟨record, start, length, startEq, lengthEq, Or.inr ⟨array, low, aligned, positive, room⟩⟩

end InitECandidate.Solver.Input.CurrentStartup.VarListRoom

#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListRoom.returned_room
#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListRoom.transaction
