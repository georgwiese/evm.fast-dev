import InitECandidate.Solver.GasBudget.FrameOpenProgram

namespace InitECandidate.Solver.GasBudget.FrameOpen
open Flapjack

set_option maxRecDepth 4000 in
/-- Exact live scratch remainder after frame_new; the real continuation record
adds104bytes, raising the complete frame_open reservation to bitmap+2760. -/
theorem geometry (scratch lower length : BitVec 64)
    (scratchAligned : scratch.toNat % 8 = 0) (lowerAligned : lower.toNat % 8 = 0)
    (fits : length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes length.toNat + 2760 ≤ scratch.toNat) :
    (FrameNew.finalScratch scratch length).toNat = scratch.toNat - (JumpDest.bitmapBytes length.toNat + 1632) ∧
    (FrameNew.finalScratch scratch length).toNat % 8 = 0 ∧
    (FrameNew.memoryPointer lower).toNat + 104 ≤ (FrameNew.finalScratch scratch length).toNat ∧
    (FrameNew.finalScratch scratch length).toNat ≤ (FrameNew.framePointer scratch).toNat := by
  have bg := JumpDest.bytes_geometry length.toNat
  obtain ⟨frameNumber, frameAligned, stackNumber, stackAligned, memoryNumber, memoryAligned,
    frameFits, firstRoom, laterRoom, suffixRoom, stackOrder, memoryOrder⟩ :=
    FrameNew.construction_geometry scratch lower (JumpDest.bitmapBytes length.toNat) scratchAligned lowerAligned bg.2.1 (by omega)
  let bitmap := Arenas.rounded .down (FrameNew.stackPointer scratch) (JumpDest.bytesWord length)
  have bitmapGeo := FrameNew.bitmap_geometry (FrameNew.stackPointer scratch) (FrameNew.memoryPointer lower)
    length stackAligned fits suffixRoom
  have bitmapNumber : bitmap.toNat = (FrameNew.stackPointer scratch).toNat - JumpDest.bitmapBytes length.toNat := bitmapGeo.2.1
  have logGeo := FrameNew.log_geometry bitmap (FrameNew.memoryPointer lower) bitmapGeo.2.2.1 bitmapGeo.2.2.2
  let buffer := ScratchList.buffer bitmap 32#64
  have bufferNumber : buffer.toNat = bitmap.toNat - 56 := logGeo.2.2.2.1
  have bufferAligned : buffer.toNat % 8 = 0 := logGeo.2.2.2.2.1
  have bufferRoom : (FrameNew.memoryPointer lower).toNat + 272 ≤ buffer.toNat := logGeo.2.2.2.2.2
  have finalNumber : (FrameNew.finalScratch scratch length).toNat = buffer.toNat - 272 := Arenas.cursor_number buffer 272 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end InitECandidate.Solver.GasBudget.FrameOpen

#print axioms InitECandidate.Solver.GasBudget.FrameOpen.geometry
