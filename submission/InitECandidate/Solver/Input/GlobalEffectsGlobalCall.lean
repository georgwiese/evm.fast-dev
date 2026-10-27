import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real helper call assigning another global preserves the tracked global
and code on every outcome, including failed operands, shapes and assignments. -/
theorem global_called (key : MlS) (code) (destination function : MlS) (arguments : List (ExpHOL 64))
    (other : key ≠ destination)
    (calleePure : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values =
      some (body, callee, shape) → Preserves key code body) :
    Preserves key code (.call (some (some (.global, destination), none)) function arguments) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]
        rfl
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by
          rw [← installed]
          exact called
        have frame := calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame ⊢
        obtain ⟨result, target⟩ := output
        have postFrame : erase key target = erase key source := frame
        cases result with
        | none => exact postFrame
        | some result =>
          cases result with
          | returned returned =>
            simp only
            split
            · split
              · simpa [erase, setKvarHOLFinite, setGlobalHOLFinite, HolFiniteMapExact.update,
                  FUPDATE, other, Ne.symm other] using postFrame
              · exact postFrame
            · exact postFrame
          | error => exact postFrame
          | timeOut => exact postFrame
          | «break» => exact postFrame
          | «continue» => exact postFrame
          | exception identifier payload => exact postFrame
          | finalFfi event => exact postFrame

theorem global_call_body (key : MlS) (code) (destination function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (other : key ≠ destination) (entry : code.lookup function = some (formals, body, shape))
    (pureBody : Preserves key code body) :
    Preserves key code (.call (some (some (.global, destination), none)) function arguments) := by
  apply global_called key code destination function arguments other
  intro values actual callee returnShape lookedUp
  rw [lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.global_called
#print axioms InitECandidate.Solver.Input.GlobalEffects.global_call_body
