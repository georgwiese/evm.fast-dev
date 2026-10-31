import InitECandidate.Solver.Mpt.StateInitRootCallTrace
import InitECandidate.Solver.Mpt.WitnessRootMaterializeNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessMaterialize WitnessCore WitnessCore.Stack

/-- The actual state_init root call resumes with its real owned root,
bounded heap, preserved node database and caller workspace. The full live
scratch contract and nonallocator globals come from that same execution. -/
theorem root_call_normal (data : Input.CurrentTable.NodeBuild.Data)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap rootHash cursor limit : BitVec 64)
    (database : Input.CurrentTable.NodeLookup.Database source data)
    (tableBefore : (Input.CurrentTable.New.endPointer data.table data.cap).toNat≤heap.toNat)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word data.table)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (scratch : Rlp.Validation.Arena source cursor limit)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source rootCall=(some (.returned returned),post)) :
    ∃ current inner node,
      Output data heap.toNat data.table current (.val (.word node)) ∧
      current.locals.lookup (ofString "root")=some (.val (.word node)) ∧ StablePrefix source current heap.toNat ∧
      current.code=source.code ∧ Rlp.LiveArena current ∧
      (∀ key,key≠ofString "heap_ptr"→key≠ofString "scratch_ptr"→current.globals.lookup key=source.globals.lookup key) ∧
      evaluateHOLFiniteState current afterRoot=(some (.returned returned),inner) ∧ post=restore source "root" inner ∧
      current.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) rootArguments=
      some (WitnessDecodeRoot.values data.table rootHash):=by
    simp [rootArguments,WitnessDecodeRoot.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nodesCell,rootCell]
  obtain ⟨callee,called,entryDb,entryRoot⟩:=WitnessDecodeRoot.environment source.code.lookup data.table rootHash
    (WitnessDecodeRoot.original_code source.code live.code)
  rw [shapes.2.2.2.2] at normal
  obtain ⟨funded,target,childReturn,inner,childRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post "root" .one
    (ofString "decode_witness_to_mpt") rootArguments _ WitnessDecodeRoot.body afterRoot callee .one args called returned normal
  let entry:=callEntryStateHOLFinite source callee
  have entryDatabase:=database.of_frame (show Input.LocalEffects.erase entry=Input.LocalEffects.erase source from rfl)
  have entryScratch:=scratch.of_fields source entry cursor limit rfl rfl
  have completed:=WitnessDecodeRoot.current_body_normal_live data entry target heap rootHash cursor limit entryDatabase tableBefore
    entryDb entryRoot heapCell heapArena heapBound aligned (live.of_frame rfl) entryScratch childReturn childRun
  have physical:=completed.1
  obtain ⟨nextHeap,node,valueEq,childHeap,rest⟩:=physical
  let current:=Input.CallNormal.continuationEntry source target "root" childReturn
  have currentOutput : Output data heap.toNat data.table current (.val (.word node)):=by
    rw [←valueEq]
    exact completed.1.of_erase data heap.toNat data.table target current childReturn rfl
  have currentRoot : current.locals.lookup (ofString "root")=some (.val (.word node)):=
    (Input.CallNormal.continuation_lookup_same source target "root" childReturn).trans (congrArg some valueEq)
  have currentLive : Rlp.LiveArena current:=completed.2.2.2.1.of_frame rfl
  refine ⟨current,inner,node,currentOutput,currentRoot,completed.2.1,?_,currentLive,?_,continued,endpoint,completed.2.2.1⟩
  · exact (Input.evaluation_fields entry target WitnessDecodeRoot.body (some (.returned childReturn)) childRun).2.2.2
  · exact completed.2.2.2.2

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.root_call_normal
