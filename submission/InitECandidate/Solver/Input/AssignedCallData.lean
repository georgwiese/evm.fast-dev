import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem local_data {F : Type} (source post : PanSemStateFiniteExact 64 F) (name function : MlS) (arguments : List (ExpHOL 64))
    (normal : evaluateHOLFiniteState source (.call (some (some (.local, name), none)) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape target returned,
      evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
      shapeEqHOL (shapeOfHOLExact returned) returnShape = true ∧
      post = setVarHOLFinite name returned {target with locals := source.locals} := by
  classical
  rw [evaluateHOLFiniteState_call] at normal
  cases args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments with
  | none => simp only [args] at normal; cases normal
  | some values =>
    simp only [args] at normal
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at normal; cases normal
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      simp only [called] at normal
      by_cases zero : source.clock = 0
      · rw [if_pos zero] at normal; cases normal
      · rw [if_neg zero] at normal
        generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at normal
        obtain ⟨result, target⟩ := output
        cases result with
        | none => cases normal
        | some result =>
          cases result with
          | returned returned =>
            simp only at normal
            by_cases checked : shapeEqHOL (shapeOfHOLExact returned) returnShape = true
            · rw [if_pos checked] at normal
              by_cases valid : isValidValueHOLExact source.toExact .local name returned = true
              · rw [if_pos valid] at normal
                have postEq := congrArg Prod.snd normal
                exact ⟨by omega, values, body, callee, returnShape, target, returned, rfl, called, computed, checked, postEq.symm⟩
              · rw [if_neg valid] at normal; cases normal
            · rw [if_neg checked] at normal; cases normal
          | error => cases normal
          | timeOut => cases normal
          | «break» => cases normal
          | «continue» => cases normal
          | exception identifier payload => cases normal
          | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.local_data
