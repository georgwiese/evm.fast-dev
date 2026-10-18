import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful ignored-result caller executed a real callee return and
had a positive caller clock. No callee result or execution is assumed. -/
theorem ignored_callee_return {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body, callee, shape))
    (run : evaluateHOLFiniteState source (.call (some (none, none)) function arguments) = (none, post)) :
    1 ≤ source.clock ∧ ∃ target returned, evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) := by
  classical
  have actual := evaluateHOLFiniteState_call source (some (none, none)) function arguments
  simp only [args, called] at actual
  have normal := congrArg Prod.fst (actual.symm.trans run)
  by_cases zero : source.clock = 0
  · simp only [if_pos zero] at normal
    cases normal
  · simp only [if_neg zero] at normal
    refine ⟨by omega, ?_⟩
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = output at normal
    obtain ⟨result, target⟩ := output
    cases result with
    | none => cases normal
    | some result =>
      cases result with
      | returned returned => exact ⟨target, returned, rfl⟩
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | exception identifier payload => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_callee_return
