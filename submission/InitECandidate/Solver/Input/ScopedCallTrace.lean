import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real scoped call either stops within its callee allowance or reaches
its genuine continuation with the actual checked return. This covers all
callee and enclosing outcomes, including exceptions and insufficient clocks. -/
theorem scoped_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (calleePrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (priced : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤calleePrice)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=(result,post)) :
    source.clock-post.clock≤calleePrice+1 ∨
      ∃ target returned inner,
        1≤source.clock ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) ∧
        (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤calleePrice+1 ∧
        evaluateHOLFiniteState (continuationEntry source target name returned) continuation=(result,inner) ∧ post=restore source name inner := by
  classical
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at run
    simp only [args,called,if_neg zero] at run
    have clock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at run priced clock
    obtain ⟨answer,target⟩ := output
    change source.clock-1-target.clock≤calleePrice at priced
    change target.clock≤source.clock-1 at clock
    have allowance : source.clock-target.clock≤calleePrice+1 := by omega
    have stopped (equal : target.clock=post.clock) : source.clock-post.clock≤calleePrice+1 := by omega
    cases answer with
    | none => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
    | some answer =>
      cases answer with
      | returned returned =>
        simp only at run
        split at run
        · rename_i checked
          have resultEq := congrArg Prod.fst run
          have endpoint := congrArg Prod.snd run
          exact Or.inr ⟨target,returned,(evaluateHOLFiniteState (continuationEntry source target name returned) continuation).2,
            by omega,rfl,checked,by omega,allowance,Prod.ext resultEq rfl,endpoint.symm⟩
        · exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | error => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | timeOut => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | «break» => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | «continue» => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | exception identifier value => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))
      | finalFfi event => exact Or.inl (stopped (congrArg (fun output=>output.2.clock) run))

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_trace
