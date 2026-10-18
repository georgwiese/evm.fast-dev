import InitECandidate.Solver.Input.LocalEffectsCall

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem scoped_call (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (calleePure : ∀ values body callee returnShape, lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) → Preserves code body)
    (pureContinuation : Preserves code continuation) : Preserves code (.decCall name shape function arguments continuation) := by
  classical
  intro source installed
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite]
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args]
  | some values =>
    simp only [args]
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called]
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called]
      by_cases zero : source.clock = 0
      · rw [if_pos zero]; rfl
      · rw [if_neg zero]
        have lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape) := by rw [← installed]; exact called
        have frame := calleePure values body callee returnShape lookup (callEntryStateHOLFinite source callee) installed
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at frame ⊢
        obtain ⟨result, target⟩ := output
        have postFrame : erase target = erase source := frame
        cases result with
        | none => exact postFrame
        | some result =>
          cases result with
          | returned returned =>
            simp only
            split
            · have codeEq : target.code = code := (code_of_erase source target postFrame).trans installed
              have tailFrame := pureContinuation (setVarHOLFinite name returned {target with locals := source.locals}) codeEq
              exact tailFrame.trans postFrame
            · exact postFrame
          | error => exact postFrame
          | timeOut => exact postFrame
          | «break» => exact postFrame
          | «continue» => exact postFrame
          | exception identifier payload => exact postFrame
          | finalFfi event => exact postFrame

theorem scoped_body (code) (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (formals : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : code.lookup function = some (formals, body, returnShape))
    (pureBody : Preserves code body) (pureContinuation : Preserves code continuation) :
    Preserves code (.decCall name shape function arguments continuation) := by
  apply scoped_call
  · intro values actual callee actualShape lookedUp
    rw [lookup_body code function formals body returnShape entry values actual callee actualShape lookedUp]
    exact pureBody
  · exact pureContinuation

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.scoped_call
#print axioms InitECandidate.Solver.Input.LocalEffects.scoped_body
