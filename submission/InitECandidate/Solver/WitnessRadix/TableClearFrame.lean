import InitECandidate.Solver.WitnessRadix.TableClear

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack PanSemStateFiniteExact

/-- Actual clearing preserves every ordinary word outside the used-byte
allocation, including the initial short-capacity byte-store case. -/
theorem clear_memory_away (memory : WordWrites.Memory) (be : Bool) (plan : AllocatedLayout.Plan)
    (ready : AllocatedLayout.Ready plan) (query : BitVec 64)
    (away : query.toNat < plan.table + 72 + 40 * plan.capacity ∨
      plan.table + 72 + 41 * plan.capacity ≤ query.toNat) :
    clearMemory memory be plan query = memory query := by
  have fits := ready.fits
  have tableAligned := ready.tableAligned
  have usedSmall : plan.table + 72 + 40 * plan.capacity < 2 ^ 64 := by omega
  have number : (usedAddress plan).toNat = plan.table + 72 + 40 * plan.capacity := by
    rw [usedAddress, BitVec.toNat_ofNat, Nat.mod_eq_of_lt usedSmall]
  by_cases four : plan.capacity = 4
  · simp only [clearMemory, if_pos four]
    apply Zero.small_memory_away memory be (usedAddress plan) query plan.capacity (by omega)
      (by rw [number]; omega) (by rw [number]; omega)
    intro same
    have numeric := congrArg BitVec.toNat same
    rw [number] at numeric
    omega
  · simp only [clearMemory, if_neg four]
    apply Zero.final_memory_away
    intro offset inside same
    have numeric := congrArg BitVec.toNat same
    rw [byteAddress_toNat (usedAddress plan) offset (by rw [number]; omega), number] at numeric
    omega

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.clear_memory_away
