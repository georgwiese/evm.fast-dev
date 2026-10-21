import InitECandidate.Solver.Input.MainRootBoundary
import InitECandidate.Solver.MutableTable.WitnessDatabaseAnyTrace
import InitECandidate.Solver.Mpt.WitnessDecodeRootProgram
import InitECandidate.Solver.Input.CallResumeFields

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessConstructors

/-- The actual root lookup either stops within its real probe allowance or
resumes with an original bounded witness slice and both databases intact.
The root pointer may be arbitrary; actual lookup execution supplies the result. -/
theorem root_lookup_call_trace (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64)
    (boundary : RootBoundary input source) (installed : OriginalCode.Installed source.code)
    (rootCell : source.locals.lookup (ofString "root_hash")=some (.val (.word root)))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Mpt.WitnessDecodeRoot.lookupCall=(outcome,post)) :
    source.clock-post.clock≤6*nodeCount input+4 ∨ ∃ nodes current answer inner,
      RootBoundary input current ∧ LocalEffects.erase current=LocalEffects.erase source ∧
      current.locals.lookup (ofString "db")=some (.val (.word nodes)) ∧ current.locals.lookup (ofString "root_hash")=some (.val (.word root)) ∧
      current.locals.lookup (ofString "r")=some (MutableTable.NodeDb.output answer) ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤6*nodeCount input+4 ∧
      (∀ slice,answer=some slice→∃ index<nodeCount input,slice=nodeSlices input index ∧ slice.2.toNat≤1024 ∧
        AllocatedBytes.Arena slice.1 slice.2.toNat ∧ 2713731432≤slice.1.toNat ∧ slice.1.toNat+slice.2.toNat≤nodes.toNat) ∧
      evaluateHOLFiniteState current Mpt.WitnessDecodeRoot.afterLookup=(outcome,inner) ∧ post=QueryBranch.restore source "r" inner := by
  have originalBoundary:=boundary
  obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) Mpt.WitnessDecodeRoot.lookupArguments=
      some (MutableTable.NodeDb.arguments nodes root) := by
    simp [Mpt.WitnessDecodeRoot.lookupArguments,MutableTable.NodeDb.arguments,QueryBranch.localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nodeCell,rootCell]
  rw [Mpt.WitnessDecodeRoot.shapes.2.2] at run
  rcases nodeDatabase.any_scoped_trace source post _ nodes (nodeCount input) 1024 (nodeSlices input) 2713717584#64 root installed "r"
      Mpt.WitnessDecodeRoot.lookupArguments Mpt.WitnessDecodeRoot.afterLookup args outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨target,answer,inner,pure,forward,spent,hit,continued,endpoint⟩ := reached
    let current:=CallNormal.continuationEntry source target "r" (MutableTable.NodeDb.output answer)
    have currentPure : LocalEffects.erase current=LocalEffects.erase source :=
      (CallNormal.continuation_erase source target "r" (MutableTable.NodeDb.output answer)).trans pure
    have currentDb : current.locals.lookup (ofString "db")=some (.val (.word nodes)) :=
      (CallNormal.continuation_lookup_other source target "r" "db" _ (by decide)).trans nodeCell
    have currentRoot : current.locals.lookup (ofString "root_hash")=some (.val (.word root)) :=
      (CallNormal.continuation_lookup_other source target "r" "root_hash" _ (by decide)).trans rootCell
    have data:=RootBoundary.erase_frame input source current originalBoundary currentPure (currentDb.trans nodeCell.symm)
    have clock : current.clock=target.clock := rfl
    exact Or.inr ⟨nodes,current,answer,inner,data,currentPure,currentDb,currentRoot,CallNormal.continuation_lookup_same _ _ _ _,by omega,by omega,hit,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.root_lookup_call_trace
