import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.MutableTable.MemoryRegion
open Flapjack PanSemStateFiniteExact WitnessRadix

theorem word_mapped (region : Region) (valid : Valid region) (offset : Nat)
    (inside : offset + 8 ≤ region.length) (aligned : offset % 8 = 0) : InitE.ordinaryDomain (byteAddress (pointer region) offset) := by
  rw [byte_address]
  have number := address_number region valid offset (by omega)
  apply BackingLayout.ordinary_mapped
  · rw [number]; have lower := valid.lower; omega
  · rw [number]; have upper := valid.upper; omega
  · rw [number]; have baseAligned := valid.aligned; simp [Nat.add_mod, baseAligned, aligned]

end InitECandidate.Solver.MutableTable.MemoryRegion

#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.word_mapped
