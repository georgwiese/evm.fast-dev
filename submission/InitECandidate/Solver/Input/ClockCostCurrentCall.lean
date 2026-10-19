import InitECandidate.Solver.Input.ClockCostCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open LocalEffects (callInfo)

/-- Concrete current callee-entry pricing for original tail, ignored and
assignment calls. No successful callee outcome is assumed. -/
theorem call_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (price : Nat)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body, callee, shape))
    (bodyCost : (callEntryStateHOLFinite source callee).clock -
      (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock ≤ price) :
    source.clock - (evaluateHOLFiniteState source (.call (callInfo destination) function arguments)).2.clock ≤ price + 1 := by
  classical
  rw [evaluateHOLFiniteState_call, args]
  simp only
  rw [called]
  simp only
  by_cases zero : source.clock = 0
  · rw [if_pos zero]
    change source.clock - source.clock ≤ _
    omega
  · rw [if_neg zero]
    have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at bodyCost bodyClock ⊢
    obtain ⟨result, target⟩ := output
    have cost : source.clock - target.clock ≤ price + 1 := by
      change source.clock - 1 - target.clock ≤ price at bodyCost
      change target.clock ≤ source.clock - 1 at bodyClock
      omega
    cases destination with
    | none =>
      cases result with
      | none => exact cost
      | some result =>
        cases result <;> simp only [callInfo, Option.map_none]
        all_goals repeat first | exact cost | split
    | some destination =>
      cases destination with
      | none =>
        cases result with
        | none => exact cost
        | some result =>
          cases result <;> simp only [callInfo, Option.map_some, Option.map_none]
          all_goals repeat first | exact cost | split
      | some name =>
        cases result with
        | none => exact cost
        | some result =>
          cases result <;> simp only [callInfo, Option.map_some]
          all_goals repeat first | exact cost | split

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.call_current
