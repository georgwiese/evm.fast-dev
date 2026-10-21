import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Observe the actual child of an ordinary ignored call at a sequence
boundary. All outcomes are covered, and only a genuine checked child return
enters the real caller continuation with restored caller locals. -/
theorem ignored_sequence_observe (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call (some (none,none)) function arguments) continuation)=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ childResult target,
      1≤source.clock ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(childResult,target) ∧
      (post.clock=target.clock ∨ ∃ value,
        childResult=some (.returned value) ∧ shapeEqHOL (shapeOfHOLExact value) shape=true ∧
        evaluateHOLFiniteState {target with locals:=source.locals} continuation=(outcome,post)) := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_call,args] at run
    simp only at run
    rw [called] at run
    simp only [if_neg zero] at run
    generalize childRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at run
    obtain ⟨answer,target⟩ := output
    refine Or.inr ⟨answer,target,by omega,rfl,?_⟩
    cases answer with
    | none => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
    | some answer =>
      cases answer with
      | returned value =>
        simp only at run
        by_cases checked : shapeEqHOL (shapeOfHOLExact value) shape=true
        · rw [if_pos checked] at run
          simp only at run
          exact Or.inr ⟨value,rfl,checked,run⟩
        · rw [if_neg checked] at run
          exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | _ => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_sequence_observe
