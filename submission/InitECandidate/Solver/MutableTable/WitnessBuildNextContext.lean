import InitECandidate.Solver.MutableTable.WitnessBuildContext
import InitECandidate.Solver.WitnessRadix.ConstructorPreparedContext

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Updating the cursor after one actual constructor preserves the complete
hash/set environment for a different decoded witness array and allocation. -/
theorem Context.after_allocation (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (allocation plan : AllocatedLayout.Plan) (slices : Nat → Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat)
    (context : Context source plan slices stp pad scratch maximum) :
    Context (Constructor.preparedState source allocation) plan slices stp pad scratch maximum := by
  refine ⟨?_,context.keccakCode,Constructor.prepared_environment source allocation stp pad context.environment,
    context.buffers,context.before,context.aligned,context.little,context.hashCode,context.copyCode,
    context.insertCode,context.memeqCode,context.findCode,context.setCode,context.lengthBound⟩
  exact (Constructor.prepared_global_other source allocation (ofString "mpt_hash_scratch") (by decide)).trans context.global

/-- The checked complete constructor result, including all real hash events,
transports the second constructor's context. Memory is intentionally absent:
its actual decoded record cells are transported separately by own frames. -/
theorem Context.after_constructor (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (allocation plan : AllocatedLayout.Plan) (slices : Nat → Graph.Slice) (stp pad scratch : BitVec 64) (maximum : Nat)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (Constructor.preparedState source allocation))
    (context : Context source plan slices stp pad scratch maximum) : Context target plan slices stp pad scratch maximum :=
  Context.of_control (Constructor.preparedState source allocation) target plan slices stp pad scratch maximum control
    (Context.after_allocation source allocation plan slices stp pad scratch maximum context)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Context.after_allocation
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Context.after_constructor
