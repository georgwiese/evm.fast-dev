import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Price a declaration only at its actual successfully checked value.
Failed reads or shape checks stop immediately and spend no source ticks. -/
theorem declared_reached_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (shape : ShapeHOL) (expression : ExpHOL 64) (body : ProgHOL 64) (price : Nat)
    (priced : ∀ value,eval source expression=some value → shapeEqHOL shape (shapeOfHOLExact value)=true →
      (setVarHOLFinite name value source).clock-(evaluateHOLFiniteState (setVarHOLFinite name value source) body).2.clock≤price) :
    source.clock-(evaluateHOLFiniteState source (.dec name shape expression body)).2.clock≤price := by
  rw [evaluateHOLFiniteState_dec_total]
  cases read : @evalHOLExact 64 Guest.HostMemory _ source.toExact
      (fun address=>Classical.propDecidable (source.memaddrs address)) expression with
  | none=>simp [read]
  | some value=>
    simp only [read]
    by_cases checked : shapeEqHOL shape (shapeOfHOLExact value)=true
    · rw [if_pos checked]
      exact priced value read checked
    · rw [if_neg checked]
      change source.clock-source.clock≤price
      omega

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.declared_reached_current
