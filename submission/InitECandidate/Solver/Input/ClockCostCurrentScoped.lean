import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price the concrete current callee entry. A parent can derive this local
allowance from its current mapped operands rather than all possible locals. -/
theorem scoped_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (calleePrice continuationPrice : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape))
    (calleeBound : (callEntryStateHOLFinite source callee).clock -
      (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock ≤ calleePrice)
    (continuationBound : Bound source.code continuation continuationPrice) :
    source.clock - (evaluateHOLFiniteState source (.decCall name shape function arguments continuation)).2.clock ≤
      calleePrice + continuationPrice + 1 := by
  classical
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args, called]
  by_cases zero : source.clock = 0
  · rw [if_pos zero]
    change source.clock - source.clock ≤ _
    omega
  · rw [if_neg zero]
    have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at calleeBound bodyClock ⊢
    obtain ⟨result, target⟩ := output
    have cost : source.clock - target.clock ≤ calleePrice + continuationPrice + 1 := by
      change source.clock - 1 - target.clock ≤ calleePrice at calleeBound
      change target.clock ≤ source.clock - 1 at bodyClock
      omega
    cases result with
    | none => exact cost
    | some result =>
      cases result with
      | returned returned =>
        simp only
        split
        · have targetCode := (Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) computed).2.2.2
          have codeEq : target.code = source.code := targetCode
          let ready := setVarHOLFinite name returned {target with locals := source.locals}
          have tailCost := continuationBound ready codeEq
          have tailClock := evaluateHOLFiniteState_clock_le ready continuation
          change target.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ continuationPrice at tailCost
          change (evaluateHOLFiniteState ready continuation).2.clock ≤ target.clock at tailClock
          change source.clock - (evaluateHOLFiniteState ready continuation).2.clock ≤ _
          change source.clock - 1 - target.clock ≤ calleePrice at calleeBound
          change target.clock ≤ source.clock - 1 at bodyClock
          omega
        · exact cost
      | error => exact cost
      | timeOut => exact cost
      | «break» => exact cost
      | «continue» => exact cost
      | exception identifier payload => exact cost
      | finalFfi event => exact cost

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scoped_current
