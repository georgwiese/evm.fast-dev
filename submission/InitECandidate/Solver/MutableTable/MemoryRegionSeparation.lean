import InitECandidate.Solver.MutableTable.MemoryRegion

namespace InitECandidate.Solver.MutableTable.MemoryRegion
open Flapjack WitnessRadix

theorem byte_address_injective (region : Region) (valid : Valid region) (first second : Nat)
    (firstInside : first ≤ region.length) (secondInside : second ≤ region.length)
    (same : byteAddress (pointer region) first = byteAddress (pointer region) second) : first = second := by
  have numeric := congrArg BitVec.toNat same
  rw [byte_address, byte_address, address_number region valid first firstInside, address_number region valid second secondInside] at numeric
  omega

theorem separate (first second : Region) (firstValid : Valid first) (secondValid : Valid second)
    (apart : first.start + first.length ≤ second.start ∨ second.start + second.length ≤ first.start)
    (offset other : Nat) (inside : offset < first.length) (otherInside : other < second.length) :
    byteAddress (pointer first) offset ≠ byteAddress (pointer second) other := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [byte_address, byte_address, address_number first firstValid offset (by omega), address_number second secondValid other (by omega)] at numeric
  omega

end InitECandidate.Solver.MutableTable.MemoryRegion

#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.byte_address_injective
#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.separate
