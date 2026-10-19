import InitECandidate.Solver.Input.AssignedCallData
import InitECandidate.Solver.Input.EvaluationFields

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real normal assigned caught call, whose actual handler cannot pass,
must have received the real callee return. The handler premise only needs
the code table actually retained by evaluation, not arbitrary foreign code. -/
theorem assigned_caught_stops (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (stops : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=source.code →
      (evaluateHOLFiniteState current handler).1≠none)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,destination),some (identifier,parameter,handler))) function arguments)=(none,post)) :
    1≤source.clock ∧ ∃ target value,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target) ∧
      shapeEqHOL (shapeOfHOLExact value) shape=true ∧ post=setVarHOLFinite destination value {target with locals:=source.locals} := by
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
        by_cases checked : shapeEqHOL (shapeOfHOLExact value) shape=true
        · rw [if_pos checked] at normal
          by_cases valid : isValidValueHOLExact source.toExact .local destination value=true
          · rw [if_pos valid] at normal
            exact ⟨by omega,target,value,rfl,checked,(congrArg Prod.snd normal).symm⟩
          · rw [if_neg valid] at normal
            cases normal
        · rw [if_neg checked] at normal
          cases normal
      | exception exceptionId value =>
        have fields := Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.exception exceptionId value)) computed
        simp only at normal
        split at normal
        · split at normal
          · split at normal
            · let ready := setVarHOLFinite parameter value {target with locals:=source.locals}
              have codeEq : ready.code=source.code := fields.2.2.2
              exact (stops ready codeEq (congrArg Prod.fst normal)).elim
            · cases normal
          · cases normal
        · cases normal
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.assigned_caught_stops
