import InitECandidate.Solver.Input.BytesList.Program
import InitECandidate.Solver.Input.VarList.RoomFromReturn
import InitECandidate.Solver.Input.NormalCallClock

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real byte-list return exposes its actual split-list allocation. The
room conclusion uses the persistent allocator's real ceiling, not a geometric
bound that assumes the forthcoming allocation succeeds. -/
theorem room_from_return (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer limit : BitVec 64) (start length floor : Nat)
    (allocCode : source.code.lookup (ofString "alloc") = some (WitnessRadix.PersistentAlloc.formals, WitnessRadix.PersistentAlloc.body, .one))
    (trapCode : source.code.lookup (ofString "trap_with") = some (Trap.formals, Trap.body, .one))
    (failCode : source.code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one))
    (exceptionShape : source.eshapes.lookup (ofString "SszErr") = some .one)
    (varCode : source.code.lookup (ofString "ssz_split_var_list") = some (VarList.formals, VarList.body, VarList.returnShape))
    (heap : NormalHeapEffects.AtLeast floor source)
    (image : Blob.HeapInput source input pointer) (inside : start + length ≤ input.length % 2^64)
    (p : source.locals.lookup (ofString "p") = some (.val (.word (pointer + BitVec.ofNat 64 start))))
    (n : source.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 length))))
    (l : source.locals.lookup (ofString "lim") = some (.val (.word limit)))
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    length = 0 ∨
      (∃ array : BitVec 64, source.globals.lookup (ofString "heap_ptr") = some (.val (.word array)) ∧
        floor ≤ array.toNat ∧ array.toNat % 8 = 0 ∧
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) := by
  have normal := actual
  rw [body_shape] at normal
  have positive := CallNormal.normal_clock source post (ofString "r") VarList.returnShape
    (ofString "ssz_split_var_list") arguments tail value normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments =
      some (VarList.values (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, arguments, VarList.values, localVar, p, n, l]
  obtain ⟨callee, called, pCell, nCell, lCell⟩ := VarList.environment source.code.lookup
    (pointer + BitVec.ofNat 64 start) (BitVec.ofNat 64 length) limit varCode
  obtain ⟨target, returned, calleeRun⟩ := CallNormal.callee_return source post (ofString "r") VarList.returnShape
    (ofString "ssz_split_var_list") arguments _ VarList.body tail callee VarList.returnShape args called positive value normal
  rcases VarList.room_from_return input (callEntryStateHOLFinite source callee) target pointer limit start length floor
    allocCode trapCode failCode exceptionShape heap image inside pCell nCell lCell returned calleeRun with empty | allocated
  · exact Or.inl empty.1
  · obtain ⟨array, cell, low, aligned, minimum, countPositive, header, upper, countLimit, room⟩ := allocated
    exact Or.inr ⟨array, cell, low, aligned, room⟩

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.room_from_return
