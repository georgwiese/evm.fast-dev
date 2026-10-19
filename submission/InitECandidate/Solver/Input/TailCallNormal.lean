import InitECandidate.Solver.Input.CallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual tail return exposes the real callee return, checked shape,
positive call clock and exact caller scope clearing. -/
theorem tail_callee_return (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.call none function arguments)=(some (.returned value),post)) :
    1≤source.clock ∧ ∃ target,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned value),target) ∧
      shapeEqHOL (shapeOfHOLExact value) shape=true ∧ post=emptyLocalsHOLFinite target := by
  classical
  rw [evaluateHOLFiniteState_call,args] at normal
  simp only [called] at normal
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
      | returned returned =>
        simp only at normal
        split at normal
        · rename_i valid
          have resultEq := congrArg Prod.fst normal
          have same : returned=value := by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq
          rw [same] at computed valid
          exact ⟨by omega,target,by rw [same],valid,(congrArg Prod.snd normal).symm⟩
        · cases normal
      | error => cases normal
      | timeOut => cases normal
      | «break» => cases normal
      | «continue» => cases normal
      | exception identifier payload => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.tail_callee_return
