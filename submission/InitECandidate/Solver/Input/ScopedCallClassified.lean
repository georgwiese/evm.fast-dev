import InitECandidate.Solver.Input.ScopedCallTrace

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A priced stopped scoped call cannot return from its enclosing function.
An enclosing return instead exposes the same actual checked callee and
continuation, even when its total clock fits the stopped allowance. -/
theorem scoped_classified (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (calleePrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape))
    (priced : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤calleePrice)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation)=(result,post)) :
    (source.clock-post.clock≤calleePrice+1 ∧ ∀ value,result≠some (.returned value)) ∨
      ∃ target returned inner,
        1≤source.clock ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) ∧
        (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true ∧
        target.clock≤source.clock ∧ source.clock-target.clock≤calleePrice+1 ∧
        evaluateHOLFiniteState (continuationEntry source target name returned) continuation=(result,inner) ∧ post=restore source name inner := by
  classical
  by_cases normal : ∃ value,result=some (.returned value)
  · obtain ⟨value,rfl⟩:=normal
    obtain ⟨funded,target,returned,inner,bodyRun,checked,continued,endpoint⟩:=
      scoped_normal source post name shape function arguments values body continuation callee returnShape args called value run
    have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    rw [bodyRun] at priced forward
    change source.clock-1-target.clock≤calleePrice at priced
    change target.clock≤source.clock-1 at forward
    exact Or.inr ⟨target,returned,inner,funded,bodyRun,checked,by omega,by omega,continued,endpoint⟩
  · rcases scoped_trace source post name shape function arguments values body continuation callee returnShape calleePrice args called priced result run with stopped|reached
    · exact Or.inl ⟨stopped,by intro value same; exact normal ⟨value,same⟩⟩
    · exact Or.inr reached

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_classified
