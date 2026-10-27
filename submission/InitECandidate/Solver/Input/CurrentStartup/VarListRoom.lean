import InitECandidate.Solver.Input.VarList.RoomFromReturn
import InitECandidate.Solver.Input.CurrentStartup.TransactionEntry
import InitECandidate.Solver.Input.VarList.NormalEntry
import InitECandidate.Solver.Input.VarList.EncodedCount

namespace InitECandidate.Solver.Input.CurrentStartup.VarListRoom
variable {decoderOrigin : DecoderOrigin}
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
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) :=
  VarList.room_from_return input source post pointer limit start length floor
    (allocation_entry source.code installed) (trap_entry source.code installed)
    (CanonicalHeader.fail_code source.code installed) (shapes .SszErr) heap image inside p n l value actual

/-- Apply allocation inversion at the genuine main-derived transaction
callee. Nonempty room is bounded by the real current allocator ceiling. -/
theorem transaction (input : Guest.InputBlob) (actual : TransactionEntry.Reached (decoderOrigin := decoderOrigin) input) :
    ∃ record : BitVec 64, ∃ start length : Nat,
      start = 62 + Guest.GasLimit.le32 input 566 ∧ length = Guest.GasLimit.le32 input 570 - Guest.GasLimit.le32 input 566 ∧
      ((length = 0) ∨ ∃ array : BitVec 64,
        record.toNat + 136 ≤ array.toNat ∧ array.toNat % 8 = 0 ∧
        0 < Guest.GasLimit.le32 input start / 4 ∧
        array.toNat + 16 * (Guest.GasLimit.le32 input start / 4) ≤ 2952790016) := by
  obtain ⟨caller, entry, post, pointer, record, size, start, length, value, context, valid, installed, shapes, domain, endian,
    globals, image, heap, p, n, l, startEq, lengthEq, inside, returned, invocation⟩ := actual
  rcases returned_room input entry post pointer 9223372036854775807#64 start length (record.toNat + 136)
    installed shapes heap image inside p n l value returned with empty | allocated
  · exact ⟨record, start, length, startEq, lengthEq, Or.inl empty.1⟩
  · obtain ⟨array, cell, low, aligned, minimum, positive, header, upper, limit, room⟩ := allocated
    exact ⟨record, start, length, startEq, lengthEq, Or.inr ⟨array, low, aligned, positive, room⟩⟩

end InitECandidate.Solver.Input.CurrentStartup.VarListRoom

#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListRoom.returned_room
#print axioms InitECandidate.Solver.Input.CurrentStartup.VarListRoom.transaction
