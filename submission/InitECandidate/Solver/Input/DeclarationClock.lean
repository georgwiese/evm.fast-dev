import InitECandidate.Solver.Input.ScalarScope

namespace InitECandidate.Solver.Input.ScalarScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A known real scalar declaration spends no source tick and restores
only its local binding, whatever its actual inner outcome. -/
theorem declare_word_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (expression : ExpHOL 64)
    (word : BitVec 64) (body : ProgHOL 64) (read : eval source expression=some (.val (.word word))) :
    (evaluateHOLFiniteState source (.dec (ofString name) .one expression body)).2.clock=(evaluateHOLFiniteState (bind source name word) body).2.clock := by
  let output:=evaluateHOLFiniteState (bind source name word) body
  have actual:=declare_execute source output.2 name expression word body output.1 read rfl
  have clock:=congrArg (fun result=>result.2.clock) actual
  exact clock

end InitECandidate.Solver.Input.ScalarScope

#print axioms InitECandidate.Solver.Input.ScalarScope.declare_word_clock
