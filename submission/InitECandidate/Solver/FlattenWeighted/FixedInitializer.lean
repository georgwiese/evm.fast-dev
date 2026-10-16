import InitECandidate.Solver.FlattenWeighted.BasicClock
import InitECandidate.Solver.FlattenBound.FixedSizePilot

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Solver.FlattenBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The large literal-writing tail, after the initializer's setup call. -/
def initializationTail := InitECandidate.Proofs.BackendStages.NamedBody713_12077

theorem initializationTail_basic : basic initializationTail = true := by decide
theorem initializationTail_nodes : nodes initializationTail = 11995 := by decide
theorem initializationTail_ticks : ticks initializationTail = 1 := by decide

/-- At most 47,984 extra Lab clocks per actual execution of the literal tail,
independent of the source clock and sizes of every installed procedure. -/
theorem initializationTail_paid {C F : Type}
    (source : StackSemStateFiniteExact 64 C F) : PaidProp 11996 initializationTail source := by
  have checked := basicPaid initializationTail source initializationTail_basic
  simpa only [initializationTail_ticks, initializationTail_nodes] using checked

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.initializationTail_basic
#print axioms InitECandidate.Solver.FlattenWeighted.initializationTail_nodes
#print axioms InitECandidate.Solver.FlattenWeighted.initializationTail_ticks
#print axioms InitECandidate.Solver.FlattenWeighted.initializationTail_paid
