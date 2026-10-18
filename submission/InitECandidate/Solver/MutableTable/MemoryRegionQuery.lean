import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.MutableTable.MemoryRegion
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Logical keys at arbitrary strides in one owned input buffer, including
queries that alternate between word-aligned and half-word-aligned starts. -/
theorem strided_query (source : PanSemStateFiniteExact 64 Guest.HostMemory) (region : Region) (valid : Valid region)
    (step index width : Nat) (fits : step * index + width ≤ region.length) (domain : source.memaddrs = InitE.ordinaryDomain) :
    (BitVec.ofNat 64 (region.start + step * index)).toNat + width < 2 ^ 64 ∧
      ∀ offset < width, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress (BitVec.ofNat 64 (region.start + step * index)) offset)) := by
  have upper := valid.upper
  have baseSmall : region.start + step * index < 2 ^ 64 := by omega
  constructor
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt baseSmall]
    omega
  · intro offset inside
    rw [domain]
    have mapped := byte_mapped region valid (step * index + offset) (by omega)
    have same : byteAddress (BitVec.ofNat 64 (region.start + step * index)) offset = byteAddress (pointer region) (step * index + offset) := by
      simp only [byteAddress, pointer, ← BitVec.ofNat_add, Nat.add_assoc]
    rw [same]
    exact mapped

end InitECandidate.Solver.MutableTable.MemoryRegion

#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.strided_query
