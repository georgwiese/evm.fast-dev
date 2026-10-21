import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Observe an actual scoped call before assigning its callee a cost. Every
funded call exposes the genuine child execution; its final clock is either
the child's clock or comes from the actual checked continuation. -/
theorem scoped_observe (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=(result,post)) :
    source.clock-post.clock≤1 ∨ ∃ childResult target,
      1≤source.clock ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(childResult,target) ∧
      (post.clock=target.clock ∨ ∃ returned inner,
        childResult=some (.returned returned) ∧
        (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true ∧
        evaluateHOLFiniteState (continuationEntry source target name returned) continuation=(result,inner) ∧ post=restore source name inner) := by
  classical
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [args,called,if_neg zero] at run
    generalize childRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at run
    obtain ⟨answer,target⟩ := output
    refine Or.inr ⟨answer,target,by omega,rfl,?_⟩
    cases answer with
    | none => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
    | some answer =>
      cases answer with
      | returned returned =>
        simp only at run
        split at run
        · rename_i checked
          have observed:=congrArg Prod.fst run
          have endpoint:=congrArg Prod.snd run
          exact Or.inr ⟨returned,(evaluateHOLFiniteState (continuationEntry source target name returned) continuation).2,
            rfl,checked,Prod.ext observed rfl,endpoint.symm⟩
        · exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | error => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | timeOut => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | «break» => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | «continue» => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | exception identifier value => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm
      | finalFfi event => exact Or.inl (congrArg (fun output=>output.2.clock) run).symm

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_observe
