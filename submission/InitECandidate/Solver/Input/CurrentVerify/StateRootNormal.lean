import InitECandidate.Solver.Input.CurrentVerify.StateInitCost
import InitECandidate.Solver.Input.CurrentVerify.WitnessRootFrame
import InitECandidate.Solver.Mpt.CurrentStateInitPrefixNormal

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The same actual state-init root call supplies a bounded/fresh scalar
node and its complete persistent frame to the original afterRoot suffix. -/
theorem state_root_normal_trace {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si array table cap root heap : BitVec 64} {start length boundary : Nat}
    (witness : CurrentStartup.WitnessArrays.Image input source pointer si array start length boundary 40 1024 (2^31))
    (tableImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} source (VarList.decodedCount input start length))
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word table)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word root)))
    (before : boundary≤heap.toNat)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source Mpt.StateInit.rootCall=(some (.returned value),post)) :
    ∃ target node inner,
      (node=0#64 ∨ heap.toNat≤node.toNat ∧ node.toNat≤2952790016) ∧
      PersistentNormalFrame source (CallNormal.continuationEntry source target "root" (.val (.word node))) heap ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry source target "root" (.val (.word node))) Mpt.StateInit.afterRoot=(some (.returned value),inner) ∧
      post=restore source "root" inner := by
  obtain ⟨callee,called,dbLocal,rootLocal⟩:=word_pair_environment source.code.lookup (ofString "decode_witness_to_mpt")
    (ofString "db") (ofString "root_hash") Mpt.WitnessDecodeRoot.body .one table root (by decide)
    (Mpt.WitnessDecodeRoot.original_code source.code arena.code)
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) Mpt.StateInit.rootArguments=
      some [.val (.word table),.val (.word root)] := by
    simp [Mpt.StateInit.rootArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,nodesCell,rootCell]
  have entryWitness : CurrentStartup.WitnessArrays.Image input (callEntryStateHOLFinite source callee) pointer si array start length boundary 40 1024 (2^31):=
    witness.of_interval (by decide) (by intros; rfl)
  have entryImage : CurrentTable.NodeBuild.ImageUpTo
      {databaseData input array pointer start length boundary 1024 with table:=table,cap:=cap} (callEntryStateHOLFinite source callee) (VarList.decodedCount input start length):=
    tableImage.of_interval rfl rfl (by intros; rfl)
  rw [Mpt.StateInit.shapes.2.2.2.2] at normal
  obtain ⟨funded,target,answer,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_normal source post "root" .one (ofString "decode_witness_to_mpt")
    Mpt.StateInit.rootArguments _ Mpt.WitnessDecodeRoot.body Mpt.StateInit.afterRoot callee .one args called value normal
  obtain ⟨node,answerEq,bounds,frame⟩:=witness_root_normal_frame entryWitness entryImage dbLocal rootLocal before heapCell heapArena heapBound aligned
    (arena.of_frame rfl) answer bodyRun
  rw [answerEq] at continued
  exact ⟨target,node,inner,bounds,frame.of_erase _ _ source _ heap rfl rfl,continued,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.state_root_normal_trace
