import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuinely terminating tail call exposes the actual terminating body.
Argument, lookup, timeout and shape failures cannot supply this observation. -/
theorem tail_terminating {F : Type} (source post : PanSemStateFiniteExact 64 F)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,shape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call none function arguments) = (result,post))
    (terminal : (∃ value,result = some (.returned value)) ∨ ∃ event,result = some (.finalFfi event)) :
    1 ≤ source.clock ∧ ∃ target,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (result,target) ∧ post = emptyLocalsHOLFinite target := by
  classical
  rw [evaluateHOLFiniteState_call] at run
  simp only [args,called] at run
  by_cases zero : source.clock = 0
  · rw [if_pos zero] at run
    have same := congrArg Prod.fst run
    simp only at same
    rw [← same] at terminal
    rcases terminal with ⟨value,bad⟩ | ⟨event,bad⟩ <;> cases bad
  · rw [if_neg zero] at run
    refine ⟨by omega,?_⟩
    generalize actual : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = answer at run ⊢
    obtain ⟨bodyResult,target⟩ := answer
    cases bodyResult with
    | none =>
      have same := congrArg Prod.fst run
      simp only at same
      rw [← same] at terminal
      rcases terminal with ⟨value,bad⟩ | ⟨event,bad⟩ <;> cases bad
    | some bodyResult =>
      cases bodyResult with
      | returned value =>
        simp only at run
        by_cases typed : shapeEqHOL (shapeOfHOLExact value) shape = true
        · rw [if_pos typed] at run
          have pair := Prod.mk.inj run
          exact ⟨target,Prod.ext pair.1 rfl,pair.2.symm⟩
        · rw [if_neg typed] at run
          have same := congrArg Prod.fst run
          simp only at same
          rw [← same] at terminal
          rcases terminal with ⟨value,bad⟩ | ⟨event,bad⟩ <;> cases bad
      | finalFfi event =>
        simp only at run
        have pair := Prod.mk.inj run
        exact ⟨target,Prod.ext pair.1 rfl,pair.2.symm⟩
      | error | timeOut | «break» | «continue» | exception identifier payload =>
        have same := congrArg Prod.fst run
        simp only at same
        rw [← same] at terminal
        rcases terminal with ⟨value,bad⟩ | ⟨event,bad⟩ <;> cases bad

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.tail_terminating
