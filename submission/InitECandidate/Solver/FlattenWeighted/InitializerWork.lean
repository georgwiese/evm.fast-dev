import InitECandidate.Solver.FlattenWeighted.Work
import InitECandidate.Solver.FlattenWeighted.FixedInitializer

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack

/-- Concrete source-work derivation for the literal-writing tail. -/
theorem initializationTail_work {C F : Type}
    (source : StackSemStateFiniteExact 64 C F) : Work initializationTail source 11996 := by
  have derivation := Work.basic (source := source) initializationTail_basic
  simpa only [initializationTail_ticks, initializationTail_nodes] using derivation

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.initializationTail_work
