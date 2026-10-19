import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current callee pricing with a continuation contract derived from each
real normal callee return. This composes reached state facts without assuming
a future successful helper or a uniform model for unrelated caller states. -/
theorem scoped_reached_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (calleePrice continuationPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (bodyCost : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤calleePrice)
    (tailCost : ∀ target returned,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) →
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true →
      target.clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) continuation).2.clock≤continuationPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2.clock≤calleePrice+continuationPrice+1 := by
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  simp only [args,called]
  by_cases zero : source.clock=0
  · rw [if_pos zero]
    change source.clock-source.clock≤_
    omega
  · rw [if_neg zero]
    have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at bodyCost bodyClock ⊢
    obtain ⟨result,target⟩ := output
    have cost : source.clock-target.clock≤calleePrice+continuationPrice+1 := by
      change source.clock-1-target.clock≤calleePrice at bodyCost
      change target.clock≤source.clock-1 at bodyClock
      omega
    cases result with
    | none => exact cost
    | some result =>
      cases result with
      | returned returned =>
        simp only
        split
        · rename_i checked
          have priced := tailCost target returned computed checked
          let ready := CallNormal.continuationEntry source target name returned
          have clock := evaluateHOLFiniteState_clock_le ready continuation
          change target.clock-(evaluateHOLFiniteState ready continuation).2.clock≤continuationPrice at priced
          change (evaluateHOLFiniteState ready continuation).2.clock≤target.clock at clock
          change source.clock-(evaluateHOLFiniteState ready continuation).2.clock≤_
          change source.clock-1-target.clock≤calleePrice at bodyCost
          change target.clock≤source.clock-1 at bodyClock
          omega
        · exact cost
      | error => exact cost
      | timeOut => exact cost
      | «break» => exact cost
      | «continue» => exact cost
      | exception identifier payload => exact cost
      | finalFfi event => exact cost

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scoped_reached_current
