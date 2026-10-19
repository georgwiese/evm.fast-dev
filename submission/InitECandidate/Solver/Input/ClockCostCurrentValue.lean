import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Known tuple/scalar declaration at the current state. An invalid shape
stops without clocks; a passed declaration prices its actual initialized
body. No successful future declaration is assumed. -/
theorem declared_value_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (value : ValueHOL 64) (body : ProgHOL 64) (price : Nat)
    (read : eval source expression=some value)
    (priced : (setVarHOLFinite name value source).clock-(evaluateHOLFiniteState (setVarHOLFinite name value source) body).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.dec name shape expression body)).2.clock≤price := by
  simp only [eval] at read
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [read]
  dsimp only
  by_cases valid : shapeEqHOL shape (shapeOfHOLExact value)=true
  · rw [if_pos valid]
    exact priced
  · rw [if_neg valid]
    change source.clock-source.clock≤price
    omega

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.declared_value_current
