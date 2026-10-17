import InitECandidate.Solver.GasBudget.FrameNewGeometry

namespace InitECandidate.Solver.GasBudget.FrameNew
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Mapped aligned words in a live arena interval. This is an entry-domain
condition, independent of the values stored there. -/
def ArenaMapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower scratch : BitVec 64) : Prop :=
  ∀ query : BitVec 64, lower.toNat ≤ query.toNat → query.toNat + 8 ≤ scratch.toNat →
    query.toNat % 8 = 0 → source.memaddrs query

theorem arena_mapped_subregion (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (lower scratch pointer : BitVec 64) (size : Nat) (mapped : ArenaMapped source lower scratch)
    (start : lower.toNat ≤ pointer.toNat) (finish : pointer.toNat + size ≤ scratch.toNat)
    (aligned : pointer.toNat % 8 = 0) (offset : Nat) (inside : offset + 8 ≤ size) (offsetAligned : offset % 8 = 0) :
    source.memaddrs (WitnessRadix.byteAddress pointer offset) := by
  have number := WitnessRadix.byteAddress_toNat pointer offset (by have bound := scratch.isLt; omega)
  apply mapped
  · rw [number]; omega
  · rw [number]; omega
  · rw [number]; omega

/-- One mapped arena plus the actual allocation geometry supplies every
bitmap/log-header/delete-header/used-byte mapping required by the real helpers. -/
theorem suffix_mapped (source : PanSemStateFiniteExact 64 Guest.HostMemory) (scratch lower length : BitVec 64)
    (mapped : ArenaMapped source lower scratch) (aligned : scratch.toNat % 8 = 0)
    (fits : length.toNat + 63 < 2 ^ 64)
    (room : lower.toNat + JumpDest.bitmapBytes length.toNat + 328 ≤ scratch.toNat) :
    (∀ offset, offset + 8 ≤ JumpDest.bitmapBytes length.toNat → offset % 8 = 0 →
      source.memaddrs (WitnessRadix.byteAddress (Arenas.rounded .down scratch (JumpDest.bytesWord length)) offset)) ∧
    (∀ offset ∈ ([0, 8, 16] : List Nat), source.memaddrs (ScratchList.header
      (Arenas.rounded .down scratch (JumpDest.bytesWord length)) + BitVec.ofNat 64 offset)) ∧
    (∀ offset, offset + 8 ≤ 72 → offset % 8 = 0 →
      source.memaddrs (ScratchTable.cursor (ScratchList.buffer
        (Arenas.rounded .down scratch (JumpDest.bytesWord length)) 32#64) 72 + BitVec.ofNat 64 offset)) ∧
    source.memaddrs (ScratchTable.cursor (ScratchList.buffer
      (Arenas.rounded .down scratch (JumpDest.bytesWord length)) 32#64) 208) := by
  let bitmap := Arenas.rounded .down scratch (JumpDest.bytesWord length)
  let buffer := ScratchList.buffer bitmap 32#64
  have bitmapGeo := bitmap_geometry scratch lower length aligned fits room
  have bitmapNumber : bitmap.toNat = scratch.toNat - JumpDest.bitmapBytes length.toNat := bitmapGeo.2.1
  have bitmapAligned : bitmap.toNat % 8 = 0 := bitmapGeo.2.2.1
  have bitmapRoom : lower.toNat + 328 ≤ bitmap.toNat := bitmapGeo.2.2.2
  have logGeo := log_geometry bitmap lower bitmapAligned bitmapRoom
  have headerNumber : (ScratchList.header bitmap).toNat = bitmap.toNat - 24 := logGeo.2.2.1
  have bufferNumber : buffer.toNat = bitmap.toNat - 56 := logGeo.2.2.2.1
  have bufferAligned : buffer.toNat % 8 = 0 := logGeo.2.2.2.2.1
  have bufferRoom : lower.toNat + 272 ≤ buffer.toNat := logGeo.2.2.2.2.2
  have tableNumber : (ScratchTable.cursor buffer 72).toNat = buffer.toNat - 72 := Arenas.cursor_number buffer 72 (by omega)
  have usedNumber : (ScratchTable.cursor buffer 208).toNat = buffer.toNat - 208 := Arenas.cursor_number buffer 208 (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro offset inside offsetAligned
    exact arena_mapped_subregion source lower scratch bitmap (JumpDest.bitmapBytes length.toNat) mapped
      (by omega) (by omega) bitmapAligned offset inside offsetAligned
  · intro offset member
    apply arena_mapped_subregion source lower scratch (ScratchList.header bitmap) 24 mapped
      (by omega) (by omega) (by rw [headerNumber]; omega) offset
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide
  · intro offset inside offsetAligned
    exact arena_mapped_subregion source lower scratch (ScratchTable.cursor buffer 72) 72 mapped
      (by omega) (by omega) (by rw [tableNumber]; omega) offset inside offsetAligned
  · apply mapped
    · rw [usedNumber]; omega
    · rw [usedNumber]; omega
    · rw [usedNumber]; omega

end InitECandidate.Solver.GasBudget.FrameNew

#print axioms InitECandidate.Solver.GasBudget.FrameNew.arena_mapped_subregion
#print axioms InitECandidate.Solver.GasBudget.FrameNew.suffix_mapped
