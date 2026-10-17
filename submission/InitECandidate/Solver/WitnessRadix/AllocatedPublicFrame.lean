import InitECandidate.Solver.WitnessRadix.HelperPublicFootprint
import InitECandidate.Solver.WitnessRadix.AllocatedLayout
import InitECandidate.Solver.WitnessRadix.ConstructorPublicFrame

namespace InitECandidate.Solver.WitnessRadix.AllocatedLayout
open Flapjack BackingLayout

theorem base_after_table (plan : Plan) (pool : Pool) (privatePool : pool ≠ .records) :
    plan.table ≤ baseNat plan pool := by
  cases pool <;> simp_all [baseNat] <;> omega

theorem public_before (plan : Plan) (ready : Ready plan) (query : BitVec 64)
    (earlier : query.toNat < plan.table) : PublicWord (layout plan) query := by
  intro pool offset writable same
  have privatePool : pool ≠ .records := by intro equal; subst pool; exact False.elim writable
  have low := base_after_table plan pool privatePool
  have valid := valid plan ready
  have nowrap := valid.noWrap pool
  have bound := write_offset_bound (layout plan) valid pool offset writable
  have number := byteAddress_toNat (base (layout plan) pool) offset (by omega)
  have equalNumber := congrArg BitVec.toNat same
  change query.toNat = (byteAddress (base (layout plan) pool) offset).toNat at equalNumber
  rw [number, base_number plan ready pool] at equalNumber
  omega

theorem constructor_before (plan : Plan) (ready : Ready plan) (query : BitVec 64)
    (earlier : query.toNat < plan.table) (index : Nat) :
    ∀ entry ∈ Constructor.writeAddresses index,
      query.toNat < (base (layout plan) entry.1).toNat := by
  intro entry member
  have privatePool : entry.1 ≠ .records := by
    simp only [Constructor.writeAddresses, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  rw [base_number plan ready entry.1]
  have low := base_after_table plan entry.1 privatePool
  omega

end InitECandidate.Solver.WitnessRadix.AllocatedLayout

#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.base_after_table
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.public_before
#print axioms InitECandidate.Solver.WitnessRadix.AllocatedLayout.constructor_before
