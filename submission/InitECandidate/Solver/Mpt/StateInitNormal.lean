import InitECandidate.Solver.Mpt.StateInitRootInstalled
import InitECandidate.Solver.Mpt.StateInitWorkspace
import InitECandidate.Solver.Mpt.StateInitStorageMemory
import InitECandidate.Solver.Mpt.StateInitStorageRuntime
import InitECandidate.Solver.Mpt.StateInitBlockGlobals
import InitECandidate.Solver.Mpt.StateInitBlockOwnedNormal
import InitECandidate.Solver.Mpt.StateInitBlockOwnershipFrame
import InitECandidate.Solver.Input.EvaluationOracle

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.Main.RunAttemptConstructors WitnessMaterialize WitnessCore MutableTable MutableTable.NaturalLayout

def OtherGlobals (source post : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop:=
  ∀ key : MlS,key≠ofString "heap_ptr" → key≠ofString "ws" → key≠ofString "bs" → key≠ofString "sk_buf" →
    key≠ofString "journal_cap" → key≠ofString "journal" → key≠ofString "journal_n" → key≠ofString "ts" →
    post.globals.lookup key=source.globals.lookup key

/-- Actual initialized workspace, closed trie graph and empty storage-root
cache, seven disjoint block tables and empty reserved journal at the
genuine final heap. Caller entry reachability remains separate. -/
def Output (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) : Prop:=
  Input.OriginalCode.Installed post.code ∧ Input.OriginalScalarGlobals.Scalars post.globals ∧
    Rlp.Validation.Arena post 2713714688#64 2701135872#64 ∧ OtherGlobals source post ∧
    post.code=source.code ∧ post.memaddrs=source.memaddrs ∧ post.be=source.be ∧ post.ffi.oracle=source.ffi.oracle ∧
    ∃ heap root storageTable,post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 0 ∧ heap.toNat%8=0 ∧ WorkspaceView post workspace nodes rootHash codes root storageTable ∧
      FrozenWitnessDatabases input (QueryBranch.bind post "db" nodes) workspace.toNat ∧
      TableState post .word (fresh .word storageTable.toNat 64) [] heap.toNat storageTable.toNat ∧
      post.globals.lookup (ofString "bs")=some (.val (.word (BitVec.ofNat 64 (freshEnd .word storageTable.toNat 64)))) ∧
      ∃ registry : NodeRegistry post (PersistentAlloc.rounded workspace 40#64).toNat heap nodes,
        registry.graph.valid root ∧ registry.graph.Regions (PersistentAlloc.rounded workspace 40#64).toNat storageTable.toNat ∧
          Block.Initialized post (BitVec.ofNat 64 (freshEnd .word storageTable.toNat 64)) workspace

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem block_name : ofString "bs"∈Input.OriginalScalarGlobals.names:=by decide_cbv

set_option maxRecDepth 100000 in
set_option maxHeartbeats 400000 in
/-- Whole original322 on a genuine normal execution: construct its actual
root/workspace/storage-cache data from current input ownership and keep it
through every real remaining initialization and lexical restoration. -/
theorem body_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (workspace nodes rootHash codes : BitVec 64) (boundary : StateInitBoundary input source)
    (installed : Input.OriginalCode.Installed source.code) (scalars : Input.OriginalScalarGlobals.Scalars source.globals)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word workspace))) (heapLower : 2713731432≤workspace.toNat)
    (nodesCell : source.locals.lookup (ofString "nodedb")=some (.val (.word nodes)))
    (rootCell : source.locals.lookup (ofString "state_root")=some (.val (.word rootHash)))
    (codesCell : source.locals.lookup (ofString "codedb")=some (.val (.word codes)))
    (scratch : Rlp.Validation.Arena source 2713714688#64 2701135872#64)
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    returned=.val (.word 0#64) ∧ Output input source post workspace nodes rootHash codes := by
  obtain ⟨oldWs,wsCell⟩:=scalars _ workspace_name
  obtain ⟨emptyRoot,emptyCell⟩:=scalars _ Input.OriginalScalarGlobals.mpt_names.1
  have aligned : workspace.toNat%8=0:=by
    obtain ⟨a,n,c,h,nd,cd,nc,cc,hc,ha,al,nb,cb⟩:=boundary
    have same : h=workspace:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (hc.symm.trans heapCell)))
    rwa [same] at al
  obtain ⟨workspaceArena,current,rootInner,root,rootOutput,currentRoot,currentWs,currentInstalled,currentScalars,currentScratch,currentGlobals,stableMemory,currentFrozen,rootTail,rootEnd,rootHeap,rootHeapCell,rootRegistry,rootMember⟩:=
    root_installed_of_normal input source post workspace oldWs nodes rootHash codes emptyRoot boundary installed scalars wsCell heapCell heapLower nodesCell rootCell codesCell emptyCell scratch returned normal
  let frontier:=(PersistentAlloc.rounded workspace 40#64).toNat
  let rooted:=installedRoot current workspace root
  have physical:=rootOutput.1
  obtain ⟨actualHeap,actualRoot,actualValue,actualCell,rootHeapArena,rootHeapAligned,frontierBefore,rest⟩:=physical
  have sameHeap : actualHeap=rootHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans rootHeapCell)))
  subst actualHeap
  have workspaceBefore : workspace.toNat+40≤frontier:=(PersistentAlloc.guards workspace 40#64 workspaceArena.upper).2.2.1
  obtain ⟨storageFunded,storageArena,storageAligned,storageCell,valid,header,occupied,storageFrozen,storageRegistry,storageMembers,blockPost,blockRun,storageEnd⟩:=
    storage_normal input rooted rootInner frontier rootHeap nodes workspace rootRegistry currentFrozen currentWs workspaceArena aligned workspaceBefore frontierBefore rootHeapCell rootHeapArena rootHeapAligned currentInstalled returned rootTail
  let storageHeap:=BitVec.ofNat 64 (freshEnd .word rootHeap.toNat 64)
  have storageBound : freshEnd .word rootHeap.toNat 64≤33806089496:=valid.upper .position
  have storageNumber : storageHeap.toNat=freshEnd .word rootHeap.toNat 64:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have storageGrows : rootHeap.toNat≤storageHeap.toNat:=by rw [storageNumber,freshEnd]; omega
  have storageScalars:=storage_scalars rooted workspace rootHeap currentScalars
  have storageWs:=(storage_other rooted workspace rootHeap (ofString "ws") (by decide)).trans currentWs
  have storageT:=storage_t rooted workspace rootHeap
  have storageInstalled : Input.OriginalCode.Installed (storageReady rooted workspace rootHeap).code:=by rw [storage_code]; exact currentInstalled
  have storageView:=workspace_of_storage source current workspace nodes rootHash codes root rootHeap frontier workspaceArena aligned (by omega) currentWs workspaceBefore frontierBefore stableMemory valid
  generalize storageEq : storageReady rooted workspace rootHeap=stored at storageCell header occupied storageFrozen storageRegistry storageMembers blockRun storageScalars storageWs storageT storageInstalled storageView
  obtain ⟨oldBs,bsCell⟩:=storageScalars _ block_name
  obtain ⟨returnedEq,blockFunded,finalBound,blockResult,finalClock,finalCell,finalArena,finalAligned,finalScalars,layouts,olderMemory,postFrozen,blockRegistry,blockMembers⟩:=
    Block.body_normal input stored blockPost frontier storageHeap nodes workspace oldBs rootHeap storageRegistry storageFrozen (by omega) storageWs bsCell storageT storageCell storageArena storageAligned storageScalars storageInstalled returned blockRun
  obtain ⟨array,nodeDb,codeDb,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=storageFrozen
  have blockInitialized:=Block.initialized_of_result stored blockPost storageHeap workspace storageArena.lower storageAligned nodeData.domain nodeData.little finalBound layouts blockResult
  let finalHeap:=BitVec.ofNat 64 (storageHeap.toNat+16848200)
  have finalNumber : finalHeap.toNat=storageHeap.toNat+16848200:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have scopeMemory : post.memory=blockPost.memory:=by rw [rootEnd,storageEnd]; rfl
  have scopeGlobals : post.globals=blockPost.globals:=by rw [rootEnd,storageEnd]; rfl
  have scopeDomain : post.memaddrs=blockPost.memaddrs:=by rw [rootEnd,storageEnd]; rfl
  have scopeEndian : post.be=blockPost.be:=by rw [rootEnd,storageEnd]; rfl
  have postInitialized:=blockInitialized.of_fields blockPost post storageHeap workspace scopeGlobals scopeMemory scopeDomain scopeEndian
  have blockOther (key : MlS) (a : key≠ofString "heap_ptr") (b : key≠ofString "bs") (c : key≠ofString "sk_buf")
      (d : key≠ofString "journal_cap") (e : key≠ofString "journal") (f : key≠ofString "journal_n") (g : key≠ofString "ts") :
      blockPost.globals.lookup key=stored.globals.lookup key:=by
    rw [blockResult]
    exact Block.result_other stored storageHeap workspace key a b c d e f g
  have storedOther (key : MlS) (other : key≠ofString "heap_ptr") : stored.globals.lookup key=current.globals.lookup key:=by
    rw [←storageEq]
    exact storage_other rooted workspace rootHeap key other
  have pointer : post.globals.lookup (ofString "ws")=some (.val (.word workspace)):=by
    rw [scopeGlobals,blockOther _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact storageWs
  have memory (query : BitVec 64) (before : query.toNat<storageHeap.toNat) : post.memory query=stored.memory query:=
    (congrFun scopeMemory query).trans (olderMemory query before)
  have view:=storageView.before_frame stored post workspace nodes rootHash codes root rootHeap storageHeap.toNat (by omega) pointer memory
  have codeEq:=(Input.evaluation_fields source post body (some (.returned returned)) normal).2.2.2
  have domain:=(Input.evaluation_fields source post body (some (.returned returned)) normal).1
  have endian:=(Input.evaluation_fields source post body (some (.returned returned)) normal).2.1
  have oracle:=Input.evaluation_oracle source post body (some (.returned returned)) normal
  have postInstalled : Input.OriginalCode.Installed post.code:=by rw [codeEq]; exact installed
  have postScalars : Input.OriginalScalarGlobals.Scalars post.globals:=by rw [scopeGlobals]; exact finalScalars
  have postCursor : post.globals.lookup (ofString "scratch_ptr")=some (.val (.word 2713714688#64)):=by
    rw [scopeGlobals,blockOther _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide),storedOther _ (by decide)]
    exact currentScratch
  have otherGlobals : OtherGlobals source post:=by
    intro key notHeap notWs notBs notSk notCap notJournal notCounter notTs
    by_cases isScratch : key=ofString "scratch_ptr"
    · subst key; exact postCursor.trans scratch.cursorGlobal.symm
    · rw [scopeGlobals,blockOther key notHeap notBs notSk notCap notJournal notCounter notTs,storedOther key notHeap]
      exact (currentGlobals key notHeap isScratch).trans ((ready_fields source workspace nodes rootHash codes).2.2.2 key notHeap notWs)
  have postLimit : post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word 2701135872#64)):=
    (otherGlobals _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans scratch.limitGlobal
  have postScratch : Rlp.Validation.Arena post 2713714688#64 2701135872#64:=
    ⟨domain.trans scratch.domain,postCursor,postLimit,scratch.ordered,scratch.aligned,scratch.lower,scratch.upper⟩
  have fields:=(Input.evaluation_fields stored blockPost afterStorageTrie (some (.returned returned)) blockRun)
  have postDomain : post.memaddrs=stored.memaddrs:=scopeDomain.trans fields.1
  have postEndian : post.be=stored.be:=scopeEndian.trans fields.2.1
  have poolFrame : MemoryModel.PoolFrame stored.memory post.memory .word (fresh .word rootHeap.toNat 64):=by
    intro pool offset inside
    have number:=NaturalLayout.number .word (fresh .word rootHeap.toNat 64) valid pool offset inside
    have bound:=(fresh_bounds .word rootHeap.toNat 64 pool).2
    apply memory
    rw [number,storageNumber]
    omega
  have finalHeader:=header.of_pool_frame stored.memory post.memory .word (fresh .word rootHeap.toNat 64) 0#64 poolFrame
  have finalOccupied:=occupied.of_pool_frame stored post .word (fresh .word rootHeap.toNat 64) valid [] postDomain postEndian poolFrame
  have postHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)):=by rw [scopeGlobals]; exact finalCell
  have table : TableState post .word (fresh .word rootHeap.toNat 64) [] finalHeap.toNat rootHeap.toNat:=
    ⟨valid,by simp,finalHeader,finalOccupied,⟨6,rfl,by decide⟩,by simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using postHeap,
      by rw [finalNumber]; exact finalBound,finalAligned,
      by intro pool; have bound:=(fresh_bounds .word rootHeap.toNat 64 pool).2; rw [finalNumber,storageNumber]; omega,
      fun pool=>(fresh_bounds .word rootHeap.toNat 64 pool).1⟩
  have frozen:=postFrozen.frame input (QueryBranch.bind blockPost "db" nodes) (QueryBranch.bind post "db" nodes) workspace.toNat scopeDomain scopeEndian
    ((bind_lookup_same post "db" nodes).trans (bind_lookup_same blockPost "db" nodes).symm) (fun query _ _=>congrFun scopeMemory query)
  obtain ⟨registry,same⟩:=blockRegistry.of_fields blockPost post frontier finalHeap nodes scopeMemory scopeDomain
  have sameRoot : registry.graph.valid=rootRegistry.graph.valid:=same.trans (blockMembers.trans storageMembers)
  have member : registry.graph.valid root:=by rw [sameRoot]; exact rootMember
  have tagMemory (node : BitVec 64) (known : rootRegistry.graph.valid node) (active : node≠0#64) : post.memory node=rooted.memory node:=by
    obtain ⟨floor,nodeArena,nodeAligned,nodeBefore⟩:=rootRegistry.regions node known active
    change node.toNat+TrieWalk.nodeBytes (GasBudget.wordAt rooted.memory node)≤rootHeap.toNat at nodeBefore
    have below : node.toNat<rootHeap.toNat:=by have sizeBound:=TrieWalk.nodeBytes_bounds (GasBudget.wordAt rooted.memory node); omega
    have notStore : node≠workspace+32#64:=by
      intro equal
      have number:=byteAddress_toNat workspace 32 (by have upper:=workspaceArena.upper; omega)
      have numeric:=congrArg BitVec.toNat equal
      change node.toNat=(byteAddress workspace 32).toNat at numeric
      rw [number] at numeric
      omega
    have kept:=storage_old_word rooted workspace rootHeap node valid below notStore
    rw [storageEq] at kept
    exact (memory node (below.trans_le storageGrows)).trans kept
  have regions:=rootRegistry.regions.of_agreement rooted.memory post.memory rooted.memaddrs post.memaddrs rootRegistry.graph registry.graph frontier rootHeap.toNat sameRoot
    (by intro node known active; unfold GasBudget.wordAt; rw [tagMemory node known active])
  have bsPointer : post.globals.lookup (ofString "bs")=some (.val (.word storageHeap)):=by
    rw [scopeGlobals,blockResult]
    exact Block.result_block_pointer stored storageHeap workspace
  exact ⟨returnedEq,postInstalled,postScalars,postScratch,otherGlobals,codeEq,domain,endian,oracle,finalHeap,root,rootHeap,postHeap,finalArena,finalAligned,view,frozen,table,bsPointer,registry,member,regions,postInitialized⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.block_name
#print axioms InitECandidate.Solver.Mpt.StateInit.body_normal
