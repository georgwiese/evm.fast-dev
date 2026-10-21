import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.WitnessRadix.QueryBranch
open Flapjack PanSemStateFiniteExact

/-- Lexical local restoration retains the actual continuation's clock. -/
theorem restore_clock {F : Type} (saved current : PanSemStateFiniteExact 64 F) (name : String) :
    (restore saved name current).clock=current.clock := rfl

end InitECandidate.Solver.WitnessRadix.QueryBranch

#print axioms InitECandidate.Solver.WitnessRadix.QueryBranch.restore_clock
