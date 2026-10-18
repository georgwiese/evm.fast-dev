import InitECandidate.Solver.Input.CaughtCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Actual normal caught calls expose their real arguments and callee lookup,
then either their checked return or the genuine matching scalar exception
and normal handler. No argument success or callee execution is assumed. -/
theorem ignored_caught_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64))
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (exceptionShape : source.eshapes.lookup identifier = some .one)
    (normal : evaluateHOLFiniteState source (.call (some (none, some (identifier, parameter, handler))) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      ((∃ target returned, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
          shapeEqHOL (shapeOfHOLExact returned) returnShape = true ∧ post = {target with locals := source.locals}) ∨
       ∃ target err, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body =
          (some (.exception identifier (.val (.word err))), target) ∧
        evaluateHOLFiniteState (setVarHOLFinite parameter (.val (.word err)) {target with locals := source.locals}) handler = (none, post)) := by
  classical
  have expanded := normal
  rw [evaluateHOLFiniteState_call] at expanded
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at expanded; cases expanded
  | some values =>
    simp only [args] at expanded
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at expanded; cases expanded
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      obtain ⟨positive, cases⟩ := ignored_caught_cases source post function arguments values body callee returnShape identifier parameter handler args called exceptionShape normal
      exact ⟨positive, values, body, callee, returnShape, rfl, called, cases⟩

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_caught_data
