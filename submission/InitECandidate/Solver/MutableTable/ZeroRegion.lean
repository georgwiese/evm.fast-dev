import InitECandidate.Solver.MutableTable.MemoryRegion
import InitECandidate.Solver.WitnessRadix.ZeroNormal

namespace InitECandidate.Solver.MutableTable
open Flapjack WitnessRadix

/-- Actual aligned zeroing retains every ordinary word outside its owned
natural interval, including all previously allocated live objects. -/
theorem zero_region_outside (memory : WordWrites.Memory) (region : MemoryRegion.Region)
    (valid : MemoryRegion.Valid region) (query : BitVec 64)
    (outside : query.toNat < region.start ∨ region.start + region.length ≤ query.toNat) :
    Zero.finalMemory memory (MemoryRegion.pointer region) region.length query = memory query := by
  apply Zero.final_memory_away
  intro offset inside same
  have number := congrArg BitVec.toNat same
  rw [MemoryRegion.byte_address, MemoryRegion.address_number region valid offset (by omega)] at number
  omega

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.zero_region_outside
