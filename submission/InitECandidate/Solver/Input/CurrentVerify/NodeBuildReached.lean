import InitECandidate.Solver.Input.CurrentVerify.NodeEntry
import InitECandidate.Solver.Input.CurrentTable.NodeBuildConstructor
import InitECandidate.Solver.Input.ScopedCallObserve

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The later original codedb/main continuation remains explicit, whether
the first database stops or normally supplies its real returned value. -/
def ResumesNodes (source target post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (childResult result : Option (PanSemResultExact 64)) : Prop :=
  post.clock=target.clock ∨ ∃ returned inner,
    childResult=some (.returned returned) ∧
    (shapeEqHOL (shapeOfHOLExact returned) .one && shapeEqHOL (shapeOfHOLExact returned) .one)=true ∧
    evaluateHOLFiniteState (CallNormal.continuationEntry source target "nodedb" returned) afterNodes=(result,inner) ∧
    post=restore source "nodedb" inner

/-- Main's current physical input data supplies this exact database/hash
workspace; the already reached input frontier bounds every later table. -/
theorem table_workspace {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    CurrentTable.Workspace source (boundary+32) 2701132160#64 2701132360#64 :=
  ⟨data.arena,data.keccak,data.heap,by have h:=data.recordInside; omega⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The actual first database caller exposes its genuine child body and
its complete current constructor trace. Main's later result is never
identified with that child alone; the true continuation is retained. -/
theorem node_body_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source nodeCall=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ array start length entry target childResult,
      CurrentStartup.WitnessArrays.Image input entry pointer si array start length boundary 40 1024 (2^31) ∧
      VarList.decodedCount input start length<2^31 ∧
      CurrentTable.Workspace entry (boundary+32) 2701132160#64 2701132360#64 ∧
      LocalEffects.erase entry=LocalEffects.erase source ∧ 1≤source.clock ∧ entry.clock=source.clock-1 ∧
      entry.locals.lookup (ofString "slice_arr")=some (.val (.word (VarList.decodedArray array length))) ∧
      entry.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 (VarList.decodedCount input start length)))) ∧
      evaluateHOLFiniteState entry CurrentTable.NodeBuild.body=(childResult,target) ∧
      (entry.clock-target.clock≤36 ∨ CurrentTable.NodeBuild.ReachesTable entry target (VarList.decodedCount input start length)
        (boundary+32) 2701132160#64 2701132360#64 childResult) ∧ ResumesNodes source target post childResult outcome := by
  obtain ⟨array,start,length,callee,image,small,args,called,arrayCell,countCell⟩:=node_environment data
  rw [node_shape] at run
  rcases CallNormal.scoped_observe source post "nodedb" .one (ofString "nodedb_build") nodeArguments _ CurrentTable.NodeBuild.body afterNodes callee .one args called outcome run with stopped|observed
  · exact Or.inl stopped
  · obtain ⟨childResult,target,funded,childRun,remaining⟩:=observed
    let entry:=callEntryStateHOLFinite source callee
    have ready : CurrentTable.Workspace entry (boundary+32) 2701132160#64 2701132360#64 := (table_workspace data).of_frame rfl
    have nextImage : CurrentStartup.WitnessArrays.Image input entry pointer si array start length boundary 40 1024 (2^31) :=
      image.of_interval (by decide) (by intro query lower upper; rfl)
    have trace:=CurrentTable.NodeBuild.constructor_trace entry target (VarList.decodedCount input start length) (boundary+32) 2701132160#64 2701132360#64
      ready small countCell childResult childRun
    exact Or.inr ⟨array,start,length,entry,target,childResult,nextImage,small,ready,rfl,funded,rfl,arrayCell,countCell,childRun,trace,remaining⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.table_workspace
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.node_body_trace
