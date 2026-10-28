import InitECandidate.Solver.Input.CurrentVerify.DatabaseLookup
import InitECandidate.Solver.Input.CurrentTable.NodeBuild.ReturnedFrame
import InitECandidate.Solver.Mpt.WitnessDecodeRootAnyTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original root decoder's real empty-root test and Patricia lookup
either stop within270ticks or resume with a genuine node witness of at most
1024bytes. Every intermediate physical frame comes from the same execution. -/
theorem witness_root_lookup_trace {input : Guest.InputBlob}
    {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap root : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (installed : OriginalCode.Installed source.code)
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word table)))
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.body=(outcome,post)) :
    source.clock-post.clock≤270 ∨ ∃ current answer inner,
      LookupResult input pointer start length boundary 1024 answer ∧
      LocalEffects.erase current=LocalEffects.erase source ∧ current.clock≤source.clock ∧ source.clock-current.clock≤270 ∧
      current.locals.lookup (ofString "db")=some (.val (.word table)) ∧
      current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some answer ∧
      evaluateHOLFiniteState current Mpt.WitnessDecodeRoot.afterLookup=(outcome,inner) ∧ post.clock=inner.clock ∧
      LocalEffects.erase post=LocalEffects.erase inner := by
  rcases Mpt.WitnessDecodeRoot.lookup_trace_any source post table root installed dbCell rootCell outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨lookupSource,lookupPost,frame,forward,price,lookupDb,lookupRoot,lookupRun,endpoint⟩ := reached
    obtain ⟨imageRoot,next,count,valid,bits,left,right,keys,image,countBound⟩ := tableImage
    have nextTable : CurrentTable.NodeBuild.ImageUpTo
        {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} lookupSource (VarList.decodedCount input start length) :=
      ⟨imageRoot,next,count,valid,bits,left,right,keys,image.of_frame frame,countBound⟩
    have lookupInstalled : OriginalCode.Installed lookupSource.code := by
      have code:=congrArg PanSemStateFiniteExact.code frame
      change lookupSource.code=source.code at code
      rw [code]; exact installed
    have nextWitness := witness.of_interval (by decide) (by
      intro query lower before
      exact congrFun (LocalEffects.memory_of_erase source lookupSource frame) query)
    have args : evalListHOLFinite lookupSource (h:=fun address=>Classical.propDecidable (lookupSource.memaddrs address)) Mpt.WitnessDecodeRoot.lookupArguments=
        some [.val (.word table),.val (.word root)] := by
      simp [Mpt.WitnessDecodeRoot.lookupArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,lookupDb,lookupRoot]
    rw [Mpt.WitnessDecodeRoot.shapes.2.2] at lookupRun
    rcases database_lookup_trace_image nextWitness lookupInstalled nextTable (by decide) "r" Mpt.WitnessDecodeRoot.lookupArguments Mpt.WitnessDecodeRoot.afterLookup args outcome lookupRun with stopped|reached
    · have clock : post.clock=lookupPost.clock := by rw [endpoint]; rfl
      exact Or.inl (by rw [clock]; omega)
    · obtain ⟨target,answer,inner,result,pure,lookupForward,lookupPrice,continued,restored⟩ := reached
      let current:=CallNormal.continuationEntry lookupSource target "r" answer
      have currentFrame : LocalEffects.erase current=LocalEffects.erase source := pure.trans frame
      have currentDb : current.locals.lookup (ofString "db")=some (.val (.word table)) :=
        (CallNormal.continuation_lookup_other lookupSource target "r" "db" answer (by decide)).trans lookupDb
      have currentRoot : current.locals.lookup (ofString "root_hash")=some (.val (.word root)) :=
        (CallNormal.continuation_lookup_other lookupSource target "r" "root_hash" answer (by decide)).trans lookupRoot
      have postClock : post.clock=inner.clock := by rw [endpoint,restored]; rfl
      have postFrame : LocalEffects.erase post=LocalEffects.erase inner := by rw [endpoint,restored]; rfl
      exact Or.inr ⟨current,answer,inner,result,currentFrame,by change target.clock≤source.clock; omega,
        by change source.clock-target.clock≤270; omega,currentDb,currentRoot,CallNormal.continuation_lookup_same _ _ _ _,continued,postClock,postFrame⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.witness_root_lookup_trace
