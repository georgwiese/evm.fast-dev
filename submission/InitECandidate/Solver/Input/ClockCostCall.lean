import InitECandidate.Solver.Input.ClockCost
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open LocalEffects (callInfo)

/-- All-outcome pricing of real tail/ignored/local-result calls, including
failed lookup/shape/destination and exceptional/timeout callee results. -/
theorem called (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64)) (price : Nat)
    (calleeBound : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Bound code body price) :
    Bound code (.call (callInfo destination) function arguments) (price + 1) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; omega
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]; omega
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; change source.clock - source.clock ≤ _; omega
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by rw [← installed]; exact called
        have bodyCost := calleeBound values body callee shape lookup (callEntryStateHOLFinite source callee) installed
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

theorem call_body (code) (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL) (price : Nat)
    (entry : code.lookup function = some (formals, body, shape)) (priced : Bound code body price) :
    Bound code (.call (callInfo destination) function arguments) (price + 1) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [LocalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact priced

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.called
#print axioms InitECandidate.Solver.Input.ClockCost.call_body
