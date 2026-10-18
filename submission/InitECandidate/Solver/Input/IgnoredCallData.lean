import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual normal ignored call derives its argument/code lookup, real
callee return, positive clock and caller-local restoration. Immutable code,
memory domains, endianness and exception shapes come from the real callee. -/
theorem ignored_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS) (arguments : List (ExpHOL 64))
    (normal : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape target returned,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
      shapeEqHOL (shapeOfHOLExact returned) returnShape = true ∧ post = {target with locals := source.locals} ∧
      target.memaddrs = source.memaddrs ∧ target.be = source.be ∧ target.eshapes = source.eshapes ∧ target.code = source.code := by
  classical
  rw [evaluateHOLFiniteState_call] at normal
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at normal; cases normal
  | some values =>
    simp only [args] at normal
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at normal; cases normal
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called] at normal
      by_cases zero : source.clock = 0
      · rw [if_pos zero] at normal
        cases normal
      · rw [if_neg zero] at normal
        generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at normal
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases normal
        | some result =>
          cases result with
          | returned returned =>
            simp only at normal
            by_cases valid : shapeEqHOL (shapeOfHOLExact returned) returnShape = true
            · rw [if_pos valid] at normal
              have same := congrArg Prod.snd normal
              have fields := evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.returned returned)) bodyRun
              exact ⟨by omega, values, body, callee, returnShape, target, returned, rfl, called, bodyRun, valid, same.symm,
                fields.1, fields.2.1, fields.2.2.1, fields.2.2.2⟩
            · rw [if_neg valid] at normal
              cases normal
          | error => cases normal
          | timeOut => cases normal
          | «break» => cases normal
          | «continue» => cases normal
          | exception identifier payload => cases normal
          | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_data
