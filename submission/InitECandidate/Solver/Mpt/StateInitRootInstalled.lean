import InitECandidate.Solver.Mpt.StateInitPrefixNormal
import InitECandidate.Solver.Mpt.StateInitRootStore
import InitECandidate.Solver.Mpt.StateInitReadyRuntime
import InitECandidate.Solver.Mpt.StateInitReadyHeap

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors Input.Main.WitnessConstructors WitnessMaterialize WitnessCore WitnessCore.Stack

/-- From a genuine whole state_init return, derive its real initialized
workspace, decoded/registered root and actual post-install continuation.
Both immutable databases are retained below the earlier workspace base,
so installing the workspace root is allowed to change a word above them. -/
theorem root_installed_of_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap oldWs nodes rootHash codes emptyRoot : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code)
    (wsCell : source.globals.lookup (ofString "ws")=some (.val (.word oldWs)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (heapLower : 2713731432≤heap.toNat)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (emptyCell : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64) (rootArena : AllocatedBytes.Arena rootHash 32)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    AllocatedBytes.Arena heap 40 ∧ ∃ current inner root,
      let frontier:=(PersistentAlloc.rounded heap 40#64).toNat
      RichOutput input frontier nodes current (.val (.word root)) ∧
      current.locals.lookup (ofString "root")=some (.val (.word root)) ∧
      current.globals.lookup (ofString "ws")=some (.val (.word heap)) ∧
      StablePrefix (ready source heap nodes rootHash codes) current frontier ∧
      FrozenWitnessDatabases input (QueryBranch.bind (installedRoot current heap root) "db" nodes) heap.toNat ∧
      evaluateHOLFiniteState (installedRoot current heap root) afterRootStore=(some (.returned returned),inner) ∧
      post=restore (ready source heap nodes rootHash codes) "root" inner ∧
      ∃ finalHeap,(installedRoot current heap root).globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        ∃ registry : NodeRegistry (installedRoot current heap root) frontier finalHeap nodes,registry.graph.valid root := by
  obtain ⟨codeArray,actualNodes,actualCodes,actualHeap,nodeData,codeData,actualNodeCell,actualCodeCell,actualHeapCell,heapArena,aligned,nodeBefore,codeBefore⟩:=boundary
  have sameNodes : actualNodes=nodes:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualNodeCell.symm.trans nodesCell)))
  have sameCodes : actualCodes=codes:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCodeCell.symm.trans codesCell)))
  have sameHeap : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualHeapCell.symm.trans heapCell)))
  subst actualNodes
  subst actualCodes
  subst actualHeap
  obtain ⟨arena,rootRun⟩:=allocation_normal source post heap oldWs nodes rootHash codes installed wsCell heapCell nodesCell rootCell codesCell
    nodeData.domain (by omega) (by have upper:=heapArena.upper; omega) aligned returned normal
  let caller:=ready source heap nodes rootHash codes
  let next:=PersistentAlloc.rounded heap 40#64
  have nodeKept:=ready_database source heap nodes rootHash codes _ nodes _ (nodeCount input) 1024 (nodeSlices input) nodeData nodeBefore arena
  have codeKept:=ready_database source heap nodes rootHash codes _ codes _ (codeCount input) 65536 (codeSlices input) codeData codeBefore arena
  have geometry:=workspace_heap_geometry heap arena aligned
  have fields:=ready_fields source heap nodes rootHash codes
  have advance (table : BitVec 64) (before : MutableTable.WitnessBuild.BeforeHeap caller table heap.toNat) :
      MutableTable.WitnessBuild.BeforeHeap caller table next.toNat:=by
    obtain ⟨capacity,cell,bound⟩:=before
    exact ⟨capacity,cell,bound.trans geometry.2.2⟩
  have callerBoundary : StateInitBoundary input caller:=
    ⟨codeArray,nodes,codes,next,nodeKept.1,codeKept.1,nodesCell,codesCell,fields.2.2.1,geometry.1,geometry.2.1,
      advance nodes nodeKept.2,advance codes codeKept.2⟩
  have callerEmpty : caller.globals.lookup (ofString "empty_trie_root")=some (.val (.word emptyRoot)):=
    (fields.2.2.2 _ (by decide) (by decide)).trans emptyCell
  have callerScratch:=ready_scratch source heap nodes rootHash codes 2713714688#64 2701135872#64 scratch
  obtain ⟨current,inner,root,output,currentRoot,stableMemory,globals,continued,endpoint⟩:=root_call_rich_normal input caller post nodes next rootHash emptyRoot
    callerBoundary installed nodesCell rootCell callerEmpty fields.2.2.1 (heapLower.trans geometry.2.2) callerScratch rootArena returned rootRun
  have currentWs : current.globals.lookup (ofString "ws")=some (.val (.word heap)):=
    (globals _ (by decide) (by decide)).trans fields.2.1
  have workspaceBefore : heap.toNat+40≤next.toNat:=(PersistentAlloc.guards heap 40#64 arena.upper).2.2.1
  obtain ⟨tailRun,finalHeap,finalCell,registry,member⟩:=after_root_normal input current inner next.toNat nodes heap root output currentWs currentRoot arena aligned workspaceBefore returned continued
  have oldFrozen : FrozenWitnessDatabases input (QueryBranch.bind caller "db" nodes) heap.toNat:=
    ⟨codeArray,nodes,codes,
      nodeKept.1.of_fields caller (QueryBranch.bind caller "db" nodes) _ nodes _ _ _ _ rfl rfl rfl,
      codeKept.1.of_fields caller (QueryBranch.bind caller "db" nodes) _ codes _ _ _ _ rfl rfl rfl,
      bind_lookup_same _ _ _,nodeKept.2,codeKept.2⟩
  have physical:=output.1
  obtain ⟨physicalHeap,physicalChild,physicalValue,physicalCell,physicalArena,physicalAligned,grows,physicalScratch,frozenFresh,owned⟩:=physical
  obtain ⟨freshCodeArray,freshNodes,freshCodes,freshNodeData,freshCodeData,freshDb,freshNodeBefore,freshCodeBefore⟩:=frozenFresh
  have domain : current.memaddrs=caller.memaddrs:=freshNodeData.domain.trans nodeKept.1.domain.symm
  have endian : current.be=caller.be:=freshNodeData.little.trans nodeKept.1.little.symm
  have currentFrozen:=oldFrozen.frame input (QueryBranch.bind caller "db" nodes) (QueryBranch.bind current "db" nodes) heap.toNat domain endian
    ((bind_lookup_same current "db" nodes).trans (bind_lookup_same caller "db" nodes).symm)
    (fun query lower upper=>stableMemory query lower (upper.trans_le geometry.2.2))
  have addressNumber : (heap+24#64).toNat=heap.toNat+24:=byteAddress_toNat heap 24 (by have upper:=arena.upper; omega)
  have installedFrozen:=currentFrozen.frame input (QueryBranch.bind current "db" nodes) (QueryBranch.bind (installedRoot current heap root) "db" nodes) heap.toNat rfl rfl
    ((bind_lookup_same (installedRoot current heap root) "db" nodes).trans (bind_lookup_same current "db" nodes).symm) (by
      intro query lower upper
      have away : query≠heap+24#64:=by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [addressNumber] at numeric; omega
      exact if_neg away)
  exact ⟨arena,current,inner,root,output,currentRoot,currentWs,stableMemory,installedFrozen,tailRun,endpoint,finalHeap,finalCell,registry,member⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.root_installed_of_normal
