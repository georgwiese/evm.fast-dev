import InitECandidate.Solver.Input.ClockCostCurrentScoped
import InitECandidate.Solver.Input.NonTimeoutScopedCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Current callee pricing with a continuation contract derived from each
real normal callee return. This composes reached state facts without assuming
a future successful helper or a uniform model for unrelated caller states. -/
theorem scoped_reached_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (calleePrice continuationPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (calleeCost : ∀ result target,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(result,target) → result≠some .timeOut →
      (callEntryStateHOLFinite source callee).clock-target.clock≤calleePrice)
    (tailCost : ∀ target returned,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) →
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true →
      ∀ result final,evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) continuation=(result,final) → result≠some .timeOut →
        target.clock-final.clock≤continuationPrice)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤calleePrice+continuationPrice+1 := by
  have funded := scoped_call_non_timeout source post (ofString name) shape function arguments values body continuation callee returnShape args called result run notTimeout
  have bodyCost := calleeCost (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1
    (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2 rfl funded.2
  have wholeNotTimeout : (evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).1≠some .timeOut := by rw [run]; exact notTimeout
  have price : source.clock-(evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)).2.clock≤calleePrice+continuationPrice+1 := by
    rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at wholeNotTimeout ⊢
    simp only [args,called] at wholeNotTimeout ⊢
    by_cases zero : source.clock=0
    · rw [if_pos zero]
      change source.clock-source.clock≤_
      omega
    · rw [if_neg zero] at wholeNotTimeout ⊢
      have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
      generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at bodyCost bodyClock wholeNotTimeout ⊢
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
          simp only at wholeNotTimeout ⊢
          split
          · rename_i checked
            have actualNonTimeout := wholeNotTimeout
            rw [if_pos checked] at actualNonTimeout
            have tailNotTimeout : (evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) continuation).1≠some .timeOut := actualNonTimeout
            have priced := tailCost target returned computed checked
              (evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) continuation).1
              (evaluateHOLFiniteState (CallNormal.continuationEntry source target name returned) continuation).2 rfl tailNotTimeout
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

  rw [run] at price
  exact price

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.scoped_reached_terminating
