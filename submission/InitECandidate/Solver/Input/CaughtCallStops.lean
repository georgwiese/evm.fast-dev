import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- When the actual exception handler cannot fall through, a normal caught
ignored call must come from the real callee return. No exception-shape fact
or successful future callee execution is assumed. -/
theorem ignored_caught_stops {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (stops : ∀ current : PanSemStateFiniteExact 64 F,(evaluateHOLFiniteState current handler).1≠none)
    (normal : evaluateHOLFiniteState source (.call (some (none,some (identifier,parameter,handler))) function arguments)=(none,post)) :
    1≤source.clock ∧ ∃ target value,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target) ∧
      shapeEqHOL (shapeOfHOLExact value) shape=true ∧ post={target with locals:=source.locals} := by
  rw [evaluateHOLFiniteState_call] at normal
  simp only [args,called] at normal
  by_cases zero : source.clock=0
  · rw [if_pos zero] at normal
    cases normal
  · rw [if_neg zero] at normal
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at normal
    obtain ⟨result,target⟩ := output
    cases result with
    | none => cases normal
    | some result =>
      cases result with
      | returned value =>
        simp only at normal
        split at normal
        · rename_i checked
          exact ⟨by omega,target,value,rfl,checked,(congrArg Prod.snd normal).symm⟩
        · cases normal
      | exception exceptionId value =>
        simp only at normal
        split at normal
        · split at normal
          · split at normal
            · exact (stops _ (congrArg Prod.fst normal)).elim
            · cases normal
          · cases normal
        · cases normal
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_caught_stops
