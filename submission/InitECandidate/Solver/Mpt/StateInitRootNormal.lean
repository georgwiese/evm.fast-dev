import InitECandidate.Solver.Mpt.StateInitRootCallTrace
import InitECandidate.Solver.Mpt.WitnessRootRegistryNormal
import InitECandidate.Solver.Mpt.WitnessRootGlobals

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessMaterialize WitnessCore WitnessCore.Stack

/-- A genuine state_init root call resumes with the actual registered root,
all older workspace words intact and every nonallocator global retained.
The continuation and final lexical restoration are the actual executed ones. -/
theorem root_call_rich_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (nodes heap rootHash emptyRoot : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64) (rootArena : AllocatedBytes.Arena rootHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source rootCall=(some (.returned returned),post)) :
    ∃ current inner node,
      RichOutput input heap.toNat nodes current (.val (.word node)) ∧
      current.locals.lookup (ofString "root")=some (.val (.word node)) ∧ StablePrefix source current heap.toNat ∧
      (∀ key,key≠ofString "heap_ptr" → key≠ofString "scratch_ptr" → current.globals.lookup key=source.globals.lookup key) ∧
      evaluateHOLFiniteState current afterRoot=(some (.returned returned),inner) ∧ post=restore source "root" inner := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) rootArguments=
      some (WitnessDecodeRoot.values nodes rootHash):=by
    simp [rootArguments,WitnessDecodeRoot.values,localVar,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,nodesCell,rootCell]
  obtain ⟨callee,called,entryDb,entryRoot⟩:=WitnessDecodeRoot.environment source.code.lookup nodes rootHash
    (WitnessDecodeRoot.original_code source.code installed)
  rw [shapes.2.2.2.2] at normal
  obtain ⟨funded,target,childReturn,inner,childRun,checked,continued,endpoint⟩:=Input.CallNormal.scoped_normal source post "root" .one
    (ofString "decode_witness_to_mpt") rootArguments _ WitnessDecodeRoot.body afterRoot callee .one args called returned normal
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=RootBoundary.of_state_init input source entry boundary rfl (entryDb.trans nodesCell.symm)
  have entryArena:=scratch.of_fields source entry 2713714688#64 2701135872#64 rfl rfl
  have output:=WitnessDecodeRoot.rich_body_normal_prefix input entry target nodes heap rootHash emptyRoot entryBoundary installed entryDb entryRoot emptyCell heapCell heapLower entryArena rootArena childReturn childRun
  have physical:=output.1.1
  obtain ⟨nextHeap,node,valueEq,childHeap,rest⟩:=physical
  let current:=Input.CallNormal.continuationEntry source target "root" childReturn
  have currentOutput : RichOutput input heap.toNat nodes current (.val (.word node)):=by
    rw [←valueEq]
    exact output.1.of_erase input heap.toNat nodes target current childReturn rfl
  have currentRoot : current.locals.lookup (ofString "root")=some (.val (.word node)):=
    (Input.CallNormal.continuation_lookup_same source target "root" childReturn).trans (congrArg some valueEq)
  refine ⟨current,inner,node,currentOutput,currentRoot,?_,?_,continued,endpoint⟩
  · exact output.2
  · intro key notHeap notScratch
    have frame:=WitnessDecodeRoot.globals key source.code installed notHeap notScratch entry rfl
    rw [childRun] at frame
    exact congrArg Prod.snd frame

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.root_call_rich_normal
