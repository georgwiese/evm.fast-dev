import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price only the callee entries selected by the current arguments. Failed
argument evaluation and lookup are included without supplying a future run. -/
theorem call_arguments_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64)) (price : Nat)
    (priced : ∀ values body callee shape,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values →
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, shape) →
      (callEntryStateHOLFinite source callee).clock -
        (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock ≤ price) :
    source.clock - (evaluateHOLFiniteState source
      (.call (LocalEffects.callInfo destination) function arguments)).2.clock ≤ price + 1 := by
  cases args : evalListHOLFinite source
      (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none =>
    rw [evaluateHOLFiniteState_call]
    simp only [args]
    omega
  | some values =>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none =>
      rw [evaluateHOLFiniteState_call]
      simp only [args, called]
      omega
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      exact call_current source destination function arguments values body callee shape price
        args called (priced values body callee shape args called)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.call_arguments_current
