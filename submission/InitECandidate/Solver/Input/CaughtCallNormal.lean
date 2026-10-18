import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual normal caught ignored call either completed its real callee
return, or caught the named scalar exception and completed its real handler.
The caller clock, payload and both executions are derived from the call. -/
theorem ignored_caught_cases {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape))
    (exceptionShape : source.eshapes.lookup identifier = some .one)
    (normal : evaluateHOLFiniteState source (.call (some (none, some (identifier, parameter, handler))) function arguments) = (none, post)) :
    1 ≤ source.clock ∧
      ((∃ target returned, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
        shapeEqHOL (shapeOfHOLExact returned) returnShape = true ∧ post = {target with locals := source.locals}) ∨
      (∃ (target : PanSemStateFiniteExact 64 F) (err : BitVec 64), evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.exception identifier (.val (.word err))), target) ∧
        evaluateHOLFiniteState (setVarHOLFinite parameter (.val (.word err)) {target with locals := source.locals}) handler = (none, post))) := by
  classical
  rw [evaluateHOLFiniteState_call] at normal
  simp only [args, called] at normal
  by_cases zero : source.clock = 0
  · rw [if_pos zero] at normal
    cases normal
  · rw [if_neg zero] at normal
    refine ⟨by omega, ?_⟩
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at normal
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
          exact Or.inl ⟨target, returned, rfl, valid, same.symm⟩
        · rw [if_neg valid] at normal
          cases normal
      | exception exceptionId payload =>
        simp only at normal
        by_cases matching : exceptionId = identifier
        · subst exceptionId
          simp only [exceptionShape] at normal
          by_cases valid : (shapeEqHOL (shapeOfHOLExact payload) .one && isValidValueHOLExact source.toExact .local parameter payload) = true
          · rw [if_pos valid] at normal
            have shapePass : shapeEqHOL (shapeOfHOLExact payload) .one = true := by
              cases check : shapeEqHOL (shapeOfHOLExact payload) .one <;> simp_all
            cases payload with
            | val word =>
              cases word with
              | word err => exact Or.inr ⟨target, err, rfl, normal⟩
            | rStruct fields => simp [shapeOfHOLExact, shapeEqHOL] at shapePass
            | nStruct name fields => simp [shapeOfHOLExact, shapeEqHOL] at shapePass
          · rw [if_neg valid] at normal
            cases normal
        · rw [if_neg matching] at normal
          cases normal
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_caught_cases
