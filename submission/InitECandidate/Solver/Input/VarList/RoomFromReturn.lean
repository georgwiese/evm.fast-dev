import InitECandidate.Solver.Input.VarList.NormalEntry
import InitECandidate.Solver.Input.VarList.EncodedCount
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input.VarList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- An actually returned current list is empty, or its real allocator must
have room for16*count. Clock padding only funds guard inversion; all size/room
conclusions refer to the original state and raw input. -/
theorem room_from_return (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64) (start length floor : Nat)
    (allocCode : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Trap.formals, Trap.body, .one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (heap : NormalHeapEffects.AtLeast floor source)
    (image : Blob.HeapInput source input pointer) (inside : start + length ≤ input.length % 2^64)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    (length = 0 ∧ value = emptyValue) ∨
      (∃ array : BitVec 64, source.globals.lookup (ofString "heap_ptr") = some (.val (.word array)) ∧
        floor ≤ array.toNat ∧ array.toNat % 8 = 0 ∧ 4 ≤ length ∧
        0 < Guest.GasLimit.le32 input start / 4 ∧
        4 * (Guest.GasLimit.le32 input start / 4) = Guest.GasLimit.le32 input start ∧
        Guest.GasLimit.le32 input start ≤ length ∧ Guest.GasLimit.le32 input start / 4 ≤ limit.toNat ∧
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) := by
  let padded : PanSemStateFiniteExact 64 Guest.HostMemory := {source with clock := source.clock + 1}
  have paddedRun := panPropsEvaluateAddClockEq body source (some (.returned value)) post 1 ⟨actual, by simp⟩
  rcases normal_entry padded {post with clock := post.clock + 1} input pointer limit start length image inside p n l
    failCode exceptionShape (by dsimp [padded]; omega) value paddedRun with empty | parsed
  · exact Or.inl empty
  · obtain ⟨minimum, countPositive, header, firstUpper, countBound, inner, allocationRun, restored⟩ := parsed
    obtain ⟨array, heapCell, low, arrayBound, aligned⟩ := heap
    let count := Guest.GasLimit.le32 input start / 4
    let first := BitVec.ofNat 64 (Guest.GasLimit.le32 input start)
    let entered := bind padded "first" first
    let ready := counted entered first
    let amount := BitVec.ofNat 64 (16 * count)
    have countLocal : ready.locals.lookup (ofString "count") = some (.val (.word (BitVec.ofNat 64 count))) := by
      have encoded : countWord first = BitVec.ofNat 64 count := count_encode input start
      exact (bind_lookup_same entered "count" (countWord first)).trans
        (congrArg (fun word : BitVec 64 => some (ValueHOL.val (HolWordLab.word word))) encoded)
    have amountNat : amount.toNat = 16 * count := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Framing.le32_lt input start; dsimp [count]; omega)]
    have read : eval ready allocationExpression = some (.val (.word amount)) := by
      have actual := allocation_read ready (BitVec.ofNat 64 count) countLocal
      simpa only [← BitVec.ofNat_mul, Nat.mul_comm count 16] using actual
    have args : evalListHOLFinite ready (h := fun address => Classical.propDecidable (ready.memaddrs address)) [allocationExpression] =
        some (WitnessRadix.PersistentAlloc.values amount) := by
      simp only [eval] at read
      simp [evalListHOLFinite, evalListHOLExact, read, WitnessRadix.PersistentAlloc.values]
    obtain ⟨room, positive, after, remaining, frame⟩ := WitnessRadix.PersistentAlloc.call_normal ready inner "arr" [allocationExpression]
      allocatedTail array amount args allocCode trapCode heapCell arrayBound value allocationRun
    rw [amountNat] at room
    exact Or.inr ⟨array, heapCell, low, aligned, minimum, countPositive, header, firstUpper, countBound, room⟩

end InitECandidate.Solver.Input.VarList

#print axioms InitECandidate.Solver.Input.VarList.room_from_return
