import InitECandidate.Solver.Input.NormalHostEffects
import InitECandidate.Solver.Input.GlobalEffectsCall

namespace InitECandidate.Solver.Input.NormalHostEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Ordinary tail/ignored/assigned calls, without an exception handler. -/
def callInfo (destination : Option (Option (VarKind × MlS))) :
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) :=
  destination.map (fun name => (name, none))

/-- Only the host state at an actual returned callee matters to an ordinary
call which resumes. A failing or trapping callee need not preserve host memory. -/
theorem called (code) (destination : Option (Option (VarKind × MlS))) (function : MlS) (arguments : List (ExpHOL 64))
    (calleePure : ∀ values body callee shape, lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) → Returning code body) :
    Preserves code (.call (callInfo destination) function arguments) := by
  classical
  intro source installed resumes
  rw [evaluateHOLFiniteState_call] at resumes ⊢
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at resumes ⊢
  | some values =>
    simp only [args] at resumes ⊢
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at resumes ⊢
    | some data =>
      obtain ⟨body, callee, shape⟩ := data
      simp only [called] at resumes ⊢
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero] at resumes ⊢
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, shape) := by rw [← installed]; exact called
        have frame := calleePure values body callee shape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame resumes ⊢
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases destination <;> simp [callInfo, Resumes] at resumes
        | some result =>
          cases result with
          | returned value =>
            have bodyFrame : host target = host source := frame value rfl
            cases destination with
            | none =>
              simp only [callInfo, Option.map_none]
              split <;> exact bodyFrame
            | some destination =>
              simp only [callInfo, Option.map_some]
              split
              · cases destination with
                | none => exact bodyFrame
                | some data =>
                  obtain ⟨kind, name⟩ := data
                  simp only
                  split
                  · cases kind <;> exact bodyFrame
                  · exact bodyFrame
              · exact bodyFrame
          | error | timeOut | «break» | «continue» | exception identifier payload | finalFfi event =>
            cases destination <;> simp [callInfo, Resumes] at resumes

theorem call_body (code) (destination : Option (Option (VarKind × MlS))) (function : MlS) (arguments : List (ExpHOL 64))
    (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (shape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, shape)) (pureBody : Returning code body) :
    Preserves code (.call (callInfo destination) function arguments) := by
  apply called
  intro values actual callee returnShape lookedUp
  rw [GlobalEffects.lookup_body code function formals body shape entry values actual callee returnShape lookedUp]
  exact pureBody

/-- A lexical scoped call retains the host state only on resuming outcomes.
The real body must return, and then its actual continuation supplies the frame. -/
theorem scoped_body (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (pureBody : Returning code body) (pureContinuation : Preserves code continuation) :
    Preserves code (.decCall name shape function arguments continuation) := by
  classical
  intro source installed resumes
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at resumes ⊢
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args] at resumes ⊢
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨actual, callee, actualShape⟩ := data
      simp only [called] at resumes ⊢
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero] at resumes ⊢
        have lookup : lookupCodeHOLFinite code.lookup function values = some (actual, callee, actualShape) := by rw [← installed]; exact called
        have bodyEq := GlobalEffects.lookup_body code function formals body returnShape entry values actual callee actualShape lookup
        subst actual
        have frame := pureBody (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame resumes ⊢
        obtain ⟨result, target⟩ := output
        cases result with
        | none => simp [Resumes] at resumes
        | some result =>
          cases result with
          | returned value =>
            have bodyFrame : host target = host source := frame value rfl
            simp only at resumes ⊢
            by_cases checked : (shapeEqHOL (shapeOfHOLExact value) shape &&
                shapeEqHOL (shapeOfHOLExact value) actualShape) = true
            · rw [if_pos checked] at resumes ⊢
              have fields := evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned value)) computed
              have codeEq : target.code = code := fields.2.2.2.trans installed
              have tailFrame := pureContinuation (setVarHOLFinite name value {target with locals := source.locals}) codeEq resumes
              exact tailFrame.trans bodyFrame
            · rw [if_neg checked]; exact bodyFrame
          | error | timeOut | «break» | «continue» | exception identifier payload | finalFfi event =>
            simp [Resumes] at resumes

end InitECandidate.Solver.Input.NormalHostEffects

#print axioms InitECandidate.Solver.Input.NormalHostEffects.called
#print axioms InitECandidate.Solver.Input.NormalHostEffects.call_body
#print axioms InitECandidate.Solver.Input.NormalHostEffects.scoped_body
