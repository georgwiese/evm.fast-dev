import InitECandidate.Solver.Input.NoException
import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Actual ignored calls cannot throw if their genuinely looked-up bodies
cannot throw. Argument/code/shape failures and timeout remain possible. -/
theorem called (code) (function : MlS) (arguments : List (ExpHOL 64))
    (calleeSafe : ∀ values body callee shape,
      lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Safe code body) :
    Safe code (.call (some (none, none)) function arguments) := by
  classical
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]; simp
  | some values =>
    simp only [args]
    cases lookedUp : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [lookedUp]; simp
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [lookedUp]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; simp
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by rw [← installed]; exact lookedUp
        have safe := calleeSafe values body callee shape lookup (callEntryStateHOLFinite source callee) installed identifier payload
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at safe ⊢
        obtain ⟨result, target⟩ := output
        cases result with
        | none => simp
        | some result =>
          cases result with
          | returned value => simp only; split <;> simp
          | exception actualId actualPayload => exact safe
          | error => simp
          | timeOut => simp
          | «break» => simp
          | «continue» => simp
          | finalFfi event => simp

theorem call_body (code) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (safe : Safe code body) :
    Safe code (.call (some (none, none)) function arguments) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [LocalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact safe

end InitECandidate.Solver.Input.NoException

#print axioms InitECandidate.Solver.Input.NoException.called
#print axioms InitECandidate.Solver.Input.NoException.call_body
