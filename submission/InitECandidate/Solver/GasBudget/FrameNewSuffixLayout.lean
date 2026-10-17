import InitECandidate.Solver.ScratchList.Call
import InitECandidate.Solver.ScratchTable.Call
import InitECandidate.Solver.JumpDest.Call

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack

/-- The unchanged log list consumes24header bytes and32buffer bytes, followed
by the272-byte empty delete table. No backing list/table slots are read yet. -/
theorem log_geometry (scratch lower : BitVec 64) (aligned : scratch.toNat % 8 = 0)
    (room : lower.toNat + 328 ≤ scratch.toNat) :
    ScratchList.header scratch = scratch - 24#64 ∧
    ScratchList.buffer scratch 32#64 = scratch - 56#64 ∧
    (ScratchList.header scratch).toNat = scratch.toNat - 24 ∧
    (ScratchList.buffer scratch 32#64).toNat = scratch.toNat - 56 ∧
    (ScratchList.buffer scratch 32#64).toNat % 8 = 0 ∧
    lower.toNat + 272 ≤ (ScratchList.buffer scratch 32#64).toNat := by
  have first := Arenas.rounded_decrement scratch 0 24 24 aligned (by decide) (by decide)
    (by decide) (by decide) (by omega)
  have headerEq : ScratchList.header scratch = scratch - 24#64 := by simpa [ScratchList.header] using first
  have next := Arenas.rounded_decrement scratch 24 32 32 aligned (by decide) (by decide)
    (by decide) (by decide) (by omega)
  have bufferEq : ScratchList.buffer scratch 32#64 = scratch - 56#64 := by
    simpa only [ScratchList.buffer, headerEq] using next
  have headerNumber := Arenas.cursor_number scratch 24 (by omega)
  have bufferNumber := Arenas.cursor_number scratch 56 (by omega)
  change (scratch - 24#64).toNat = _ at headerNumber
  change (scratch - 56#64).toNat = _ at bufferNumber
  refine ⟨headerEq, bufferEq, ?_, ?_, ?_, ?_⟩
  · rw [headerEq]; exact headerNumber
  · rw [bufferEq]; exact bufferNumber
  · rw [bufferEq, bufferNumber]; omega
  · rw [bufferEq, bufferNumber]; omega

/-- Exact bitmap reservation for an aligned incoming scratch cursor. -/
theorem bitmap_geometry (scratch lower length : BitVec 64)
    (aligned : scratch.toNat % 8 = 0) (fits : length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes length.toNat + 328 ≤ scratch.toNat) :
    Arenas.rounded .down scratch (JumpDest.bytesWord length) =
        scratch - BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) ∧
    (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat = scratch.toNat - JumpDest.bitmapBytes length.toNat ∧
    (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat % 8 = 0 ∧
    lower.toNat + 328 ≤ (Arenas.rounded .down scratch (JumpDest.bytesWord length)).toNat := by
  have bytes := JumpDest.bytes_number length fits
  have geometry := JumpDest.bytes_geometry length.toNat
  have exactWord : JumpDest.bytesWord length = BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) := by
    rw [← bytes]
    simp
  have roundEq := Arenas.rounded_decrement scratch 0 (JumpDest.bitmapBytes length.toNat)
    (JumpDest.bitmapBytes length.toNat) aligned (by decide) geometry.1 (by omega) (by omega) (by omega)
  simp only [BitVec.sub_zero, Nat.zero_add] at roundEq
  have pointerEq : Arenas.rounded .down scratch (JumpDest.bytesWord length) =
      scratch - BitVec.ofNat 64 (JumpDest.bitmapBytes length.toNat) := by rw [exactWord]; exact roundEq
  have number := Arenas.cursor_number scratch (JumpDest.bitmapBytes length.toNat) (by omega)
  refine ⟨pointerEq, ?_, ?_, ?_⟩
  · rw [pointerEq]; exact number
  · rw [pointerEq, number]; omega
  · rw [pointerEq, number]; omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.log_geometry
#print axioms InitECandidate.Solver.GasBudget.FrameNew.bitmap_geometry
