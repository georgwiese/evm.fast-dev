import InitECandidate.Solver.Input.CurrentTable.NodeLookup.Call
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.ReturnedFrame
import InitECandidate.Solver.Mpt.WitnessDecodeRootAnyTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original root decoder's real empty-root test and Patricia lookup
either stop within270ticks or resume with a genuine node witness of at most
1024bytes. Every intermediate physical frame comes from the same execution. -/
theorem witness_root_lookup_trace (data : CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (database : CurrentTable.NodeLookup.Database source data) (installed : OriginalCode.Installed source.code)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body=(outcome,post)) :
    source.clock-post.clock≤270 ∨ ∃ current answer inner,
      CurrentTable.NodeLookup.Result data answer ∧
      LocalEffects.erase current=LocalEffects.erase source ∧ current.clock≤source.clock ∧ source.clock-current.clock≤270 ∧
      current.locals.lookup (ofString "db")=some (.val (.word data.table)) ∧
      current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some answer ∧
      evaluateHOLFiniteState current Mpt.WitnessDecodeRoot.afterLookup=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  rcases Mpt.WitnessDecodeRoot.lookup_trace_any source post data.table root installed dbCell rootCell outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨lookupSource,lookupPost,frame,forward,price,lookupDb,lookupRoot,lookupRun,endpoint⟩ := reached
    have nextDatabase:=database.of_frame frame
    obtain ⟨imageRoot,next,count,valid,bits,left,right,keys,image,countBound⟩:=nextDatabase.image
    have lookupInstalled : OriginalCode.Installed lookupSource.code := by
      have code:=congrArg PanSemStateFiniteExact.code frame
      change lookupSource.code=source.code at code
      rw [code]; exact installed
    have args : evalListHOLFinite lookupSource (h:=fun address=>Classical.propDecidable (lookupSource.memaddrs address)) Mpt.WitnessDecodeRoot.lookupArguments=
        some [.val (.word data.table),.val (.word root)] := by
      simp [Mpt.WitnessDecodeRoot.lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,lookupDb,lookupRoot]
    rw [Mpt.WitnessDecodeRoot.shapes.2.2] at lookupRun
    rcases CurrentTable.NodeLookup.scoped_trace data lookupSource lookupPost data.table data.cap imageRoot root next count valid bits left right keys image nextDatabase.rows lookupInstalled "r" Mpt.WitnessDecodeRoot.lookupArguments Mpt.WitnessDecodeRoot.afterLookup args outcome lookupRun with stopped|reached
    · have clock : post.clock=lookupPost.clock := by rw [endpoint]; rfl
      exact Or.inl (by rw [clock]; have lookupCost:=stopped.1; omega)
    · obtain ⟨target,answer,inner,result,pure,lookupForward,lookupPrice,continued,restored⟩ := reached
      let current:=CallNormal.continuationEntry lookupSource target "r" answer
      have currentFrame : LocalEffects.erase current=LocalEffects.erase source := pure.trans frame
      have currentDb : current.locals.lookup (ofString "db")=some (.val (.word data.table)) :=
        (CallNormal.continuation_lookup_other lookupSource target "r" "db" answer (by decide)).trans lookupDb
      have currentRoot : current.locals.lookup (ofString "root_hash")=some (.val (.word root)) :=
        (CallNormal.continuation_lookup_other lookupSource target "r" "root_hash" answer (by decide)).trans lookupRoot
      have postClock : post.clock=inner.clock := by rw [endpoint,restored]; rfl
      have postFrame : LocalEffects.erase post=LocalEffects.erase inner := by rw [endpoint,restored]; rfl
      exact Or.inr ⟨current,answer,inner,result,currentFrame,by change target.clock≤source.clock; omega,
        by change source.clock-target.clock≤270; omega,currentDb,currentRoot,CallNormal.continuation_lookup_same _ _ _ _,continued,postClock,postFrame⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_root_lookup_trace
