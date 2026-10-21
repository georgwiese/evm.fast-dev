import InitECandidate.Solver.Mpt.WitnessMaterializeEnvironment
import InitECandidate.Solver.MutableTable.NodeDbTail32
import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def MaterializeResumes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult outcome : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧ shapeEqHOL (shapeOfHOLExact returned) .one=true ∧
    evaluateHOLFiniteState (Input.CallNormal.continuationEntry source target "nd" returned) afterMaterialize=(outcome,inner) ∧
    post=QueryBranch.restore source "nd" inner

/-- The actual present slice supplies the real materializer's three-word
ABI. Observe every original callee outcome before assigning its body a cost. -/
theorem materialize_call_trace (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (db : BitVec 64) (slice : Graph.Slice)
    (installed : Input.OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (rCell : source.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output (some slice)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source materializeCall=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ entry target childResult,
      Input.LocalEffects.erase entry=Input.LocalEffects.erase source ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "db")=some (.val (.word db)) ∧ entry.locals.lookup (ofString "p")=some (.val (.word slice.1)) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word slice.2)) ∧
      evaluateHOLFiniteState entry WitnessMaterialize.body=(childResult,target) ∧ MaterializeResumes source target post childResult outcome := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) materializeArguments=
      some (WitnessMaterialize.values db slice.1 slice.2) := by
    simp [materializeArguments,WitnessMaterialize.values,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,dbCell,rCell,
      MutableTable.NodeDb.output,MutableTable.NodeDb.triple]
  obtain ⟨callee,called,dbEntry,pEntry,nEntry⟩ := WitnessMaterialize.environment source.code.lookup db slice.1 slice.2 (WitnessMaterialize.original_code source.code installed)
  rw [lookup_tail_shape.2] at run
  rcases Input.CallNormal.scoped_observe source post "nd" .one (ofString "_decode_witness_node") materializeArguments _ WitnessMaterialize.body afterMaterialize callee .one
      args called outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,resumes⟩ := reached
    refine Or.inr ⟨callEntryStateHOLFinite source callee,target,childResult,rfl,rfl,dbEntry,pEntry,nEntry,childRun,?_⟩
    rcases resumes with stopped|normal
    · exact Or.inl stopped
    · obtain ⟨returned,inner,resultEq,shape,continued,endpoint⟩ := normal
      have checked : shapeEqHOL (shapeOfHOLExact returned) .one=true := by simpa using shape
      exact Or.inr ⟨returned,inner,resultEq,checked,continued,endpoint⟩

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.materialize_call_trace
