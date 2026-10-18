import InitECandidate.Solver.MutableTable.MemoryModelPoolFrame

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- All physical cells of an earlier live table survive a mutation that
protects every word below its new table's lifetime floor. -/
theorem PoolFrame.of_protected_before (source target : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (floor : Nat) (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ floor)
    (frame : ∀ address : BitVec 64, address.toNat < floor → target address = source address) : PoolFrame source target kind plan := by
  intro pool offset inside
  apply frame
  rw [number kind plan valid pool offset inside]
  have before := earlier pool
  omega

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.PoolFrame.of_protected_before
