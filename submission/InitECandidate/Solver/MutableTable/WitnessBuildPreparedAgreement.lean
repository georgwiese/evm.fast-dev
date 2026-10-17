import InitECandidate.Solver.MutableTable.WitnessBuildPrepare
import InitECandidate.Solver.WitnessRadix.MemoryRegionAgreement

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Both real allocation/initialization prefixes preserve public words below
their common table allocation, identical events and the common heap cursor.
Earlier private tables may differ outside the selected public region. -/
theorem prepared_agrees (source right : PanSemStateFiniteExact 64 Guest.HostMemory)
    (plan : AllocatedLayout.Plan) (ready : AllocatedLayout.Ready plan)
    (region : BitVec 64 → Prop) (before : ∀ query, region query → query.toNat < plan.table)
    (same : MemoryRegion.Agree region source.memory right.memory)
    (ffi : source.ffi = right.ffi) (globals : source.globals = right.globals) :
    MemoryRegion.Agree region (prepared source plan).memory (Constructor.preparedState right plan).memory ∧
      (prepared source plan).ffi = (Constructor.preparedState right plan).ffi ∧
      (prepared source plan).globals = (Constructor.preparedState right plan).globals := by
  have memory : MemoryRegion.Agree region (prepared source plan).memory (Constructor.preparedState right plan).memory := by
    intro query inside
    change TableNew.resultMemory source.memory source.be plan query =
      TableNew.resultMemory right.memory right.be plan query
    rw [TableNew.result_earlier _ _ plan ready query (before query inside),
      TableNew.result_earlier _ _ plan ready query (before query inside)]
    exact same query inside
  have ffiEq : (prepared source plan).ffi = (Constructor.preparedState right plan).ffi := ffi
  have globalsEq : (prepared source plan).globals = (Constructor.preparedState right plan).globals := by
    change source.globals.update _ = right.globals.update _
    rw [globals]
  exact ⟨memory, ffiEq, globalsEq⟩

theorem prepared_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) :
    (prepared source plan).clock = source.clock - (TableNew.price plan.capacity + 1) := rfl

theorem radix_prepared_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : AllocatedLayout.Plan) :
    (Constructor.preparedState source plan).clock = source.clock - (TableNew.price plan.capacity + 1) := rfl

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prepared_agrees
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.prepared_clock
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.radix_prepared_clock
