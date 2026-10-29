import InitECandidate.Solver.MutableTable.MemoryRegionCore
import InitECandidate.Solver.MutableTable.NaturalLayout

namespace InitECandidate.Solver.MutableTable.MemoryRegion

theorem pool_valid (kind : KeyHash.Kind) (plan : NaturalLayout.Plan) (valid : NaturalLayout.Valid kind plan) (pool : NaturalLayout.Pool) :
    Valid ⟨plan.base pool, NaturalLayout.size kind plan pool⟩ := ⟨valid.lower pool, valid.upper pool, valid.aligned pool⟩

end InitECandidate.Solver.MutableTable.MemoryRegion

#print axioms InitECandidate.Solver.MutableTable.MemoryRegion.pool_valid
