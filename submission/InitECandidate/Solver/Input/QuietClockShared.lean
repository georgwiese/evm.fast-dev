import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Every shared-load outcome preserves the source call/loop clock, including
unmapped reads, absent host bytes, malformed operands and terminal FFI replies. -/
theorem QuietClock.shared_load (code) (operator : OpSize) (kind : VarKind)
    (name : MlS) (expression : ExpHOL 64) :
    QuietClock.Preserves code (.shMemLoad operator kind name expression) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_shMemLoad_source]
  simp only [shMemLoadHOLFiniteExact]
  repeat' first
    | rfl
    | unfold setKvarFfiHOLFinite
    | unfold setKvarHOLFinite
    | unfold setVarHOLFinite
    | unfold setGlobalHOLFinite
    | split

theorem ClockCost.shared_load (code) (operator : OpSize) (kind : VarKind)
    (name : MlS) (expression : ExpHOL 64) :
    ClockCost.Bound code (.shMemLoad operator kind name expression) 0 :=
  ClockCost.of_quiet code _ (QuietClock.shared_load code operator kind name expression)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.QuietClock.shared_load
#print axioms InitECandidate.Solver.Input.ClockCost.shared_load
