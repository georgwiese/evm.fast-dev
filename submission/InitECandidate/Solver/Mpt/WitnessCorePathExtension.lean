import InitECandidate.Solver.Mpt.WitnessCoreRegistryExtension
import InitECandidate.Solver.Mpt.WitnessNodeRegistryExtensionPaths
import InitECandidate.Solver.Mpt.WitnessCorePathTransport
import InitECandidate.Solver.Mpt.WitnessCorePathRegister

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine whole original extension return registers its real node,
borrows the pending record's full path, and retains every older pending
buffer through the actual allocation, metadata stores and record pop. -/
theorem ActiveRegistry.extension_paths_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap finalHeap cursor limit nibbles length child : BitVec 64) (entry : Entry) (rest : List Entry)
    (registry : ActiveRegistry source frontier db ⟨heap,cursor,entry::rest,.returning,true⟩) (paths : registry.PathModel)
    (view : View source db cursor.toNat heap.toNat (entry::rest)) (payload : entry.data.payload=.extension nibbles length)
    (owned : ResultOwned source entry.mark heap.toNat child) (frontierLower : 2713731432≤frontier) (frontierBefore : frontier≤heap.toNat)
    (pathFloor : frontier≤nibbles.toNat)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word entry.record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (actualHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)))
    (normal : evaluateHOLFiniteState source returnExtension=(none,post)) :
    ∃ next : ActiveRegistry post frontier db ⟨finalHeap,cursor,rest,.returning,true⟩,next.PathModel := by
  obtain ⟨next,nextCell,nextArena,nextAligned,grows,scratch,tail,returnedOwned,actualTop,actualResult,globals,locals,memory,domain,endian,code,rank,
      extensionView,frame,before⟩:=return_extension_stack_normal source post db heap cursor limit nibbles length child entry rest view payload owned
    topCell resultCell heapCell heapArena heapAligned arena installed normal
  have same : next=finalHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (nextCell.symm.trans actualHeap)))
  subst next
  have below : cursor.toNat≤2713717616:=by
    have ceiling:=(view.records entry List.mem_cons_self).ceiling
    have lower:=view.above entry List.mem_cons_self
    omega
  have above : cursor.toNat+7≤frontier:=by omega
  have path:=paths.pending entry List.mem_cons_self
  simp only [payload,WitnessRecord.Payload.PathBytes] at path
  have pathBefore:=(view.before entry List.mem_cons_self).2.trans (view.marks entry List.mem_cons_self)
  simp only [payload,WitnessRecord.Payload.endAddress] at pathBefore
  have apart : ∀ index<length.toNat,∀ owner,registry.nodes.graph.valid owner → owner≠0#64 →
      ∀ offset<TrieWalk.nodeBytes (wordAt source.memory owner),panByteAlignHOL (width:=64) (byteAddress nibbles index)≠byteAddress owner offset:=
    paths.pendingNode entry List.mem_cons_self nibbles length payload
  obtain ⟨nodes,nodesPaths,member,includes,members⟩:=registry.nodes.extension_result_paths source post frontier db heap finalHeap cursor limit nibbles length child
    paths.nodes above frontierBefore frame extensionView actualHeap before (registry.returned rfl child resultCell) path.1 path.2 pathFloor pathBefore apart
  have children:=registry.children.normal_frame source post registry.nodes.graph.valid nodes.graph.valid db heap cursor limit (entry::rest) view includes below frame
  have tags:=registry.nodes.tags_normal source post frontier heap db cursor limit (by omega) frame
  have excluded:=registry.excludes_extension source post frontier db _ view nodes.graph heap members tags (fun _=>Nat.le_refl _)
  let finalRegistry : ActiveRegistry post frontier db ⟨finalHeap,cursor,rest,.returning,true⟩:=
    ⟨nodes,children.tail post nodes.graph.valid entry rest,
      (by intro current inRest node index occupied currentPayload; exact excluded current (List.mem_cons_of_mem entry inRest) node index occupied currentPayload),
      (by intro phase node cell; have same : node=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (cell.symm.trans actualResult))); subst node; exact member)⟩
  obtain ⟨oldNodes,oldValid⟩:=registry.nodes.after_normal_frame source post frontier heap heap db cursor limit (by omega) (Nat.le_refl _) frame
  have oldNodesPaths:=paths.nodes.normal_frame source post frontier heap heap db cursor limit registry.nodes oldNodes oldValid above (Nat.le_refl _) frame
  have oldIncludes : ∀ node,registry.nodes.graph.valid node → oldNodes.graph.valid node:=by
    intro node member; rw [oldValid]; exact member
  have oldChildren:=registry.children.normal_frame source post registry.nodes.graph.valid oldNodes.graph.valid db heap cursor limit (entry::rest) view oldIncludes below frame
  have oldExcluded:=registry.excludes_same source post frontier db _ oldNodes.graph oldValid tags
  -- This old-allocation data model retains only the unpopped buffers;
  -- the actual final control state is described by finalRegistry above.
  let oldRegistry : ActiveRegistry post frontier db ⟨heap,cursor,rest,.decode,true⟩:=
    ⟨oldNodes,oldChildren.tail post oldNodes.graph.valid entry rest,
      (by intro current inRest node index occupied currentPayload; exact oldExcluded current (List.mem_cons_of_mem entry inRest) node index occupied currentPayload),
      (by intro phase; cases phase)⟩
  have agree : ∀ query,registry.nodes.graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.nodes.graph.footprint_bounds frontier heap.toNat registry.nodes.regions query required
    exact frame.memory query (by omega) bounds.2
  have pending : ∀ current∈rest,current.data.payload.PathBytes post:=by
    intro current inRest
    have sourceMember:=List.mem_cons_of_mem entry inRest
    have currentBefore:=(view.before current sourceMember).mono current.data current.mark heap.toNat (view.marks current sourceMember)
    exact (paths.pending current sourceMember).database_frame source post current.record db heap current.data (view.records current sourceMember)
      currentBefore (DatabaseFrame.of_decode source post heap cursor limit frame below)
  have oldPaths : oldRegistry.PathModel:=paths.transport source post frontier db _ _ registry oldRegistry oldNodesPaths oldValid
    (fun current inRest=>⟨current,List.mem_cons_of_mem entry inRest,rfl⟩) agree pending
  have currentMembers : ∀ current,nodes.graph.valid current → oldRegistry.nodes.graph.valid current ∨ current=heap:=by
    intro current currentMember
    rcases members current currentMember with prior|fresh
    · left; change oldNodes.graph.valid current; rw [oldValid]; exact prior
    · exact Or.inr fresh
  have fields : wordAt post.memory (heap+32#64)=nibbles ∧ wordAt post.memory (heap+40#64)=length:=by
    constructor
    · simp [wordAt,extensionView.cells (32,nibbles) (by simp),MemoryBytes.wordBits]
    · simp [wordAt,extensionView.cells (40,length) (by simp),MemoryBytes.wordBits]
  have tag : wordAt post.memory heap=2#64:=by
    simp [wordAt,MemoryBytes.wordBits,show post.memory heap=.word 2#64 from by simpa only [BitVec.add_zero] using extensionView.cells (0,2#64) (by simp)]
  have newPathApart (active : heap≠0#64) (pathTag : wordAt post.memory heap=1#64 ∨ wordAt post.memory heap=2#64) :
      ∀ index<(wordAt post.memory (heap+40#64)).toNat,∀ current∈rest,∀ owner slot occupied,current.data.payload=.branch owner slot occupied → ∀ offset<176,
        panByteAlignHOL (width:=64) (byteAddress (wordAt post.memory (heap+32#64)) index)≠byteAddress owner offset:=by
    intro index inside current inRest owner slot occupied currentPayload offset offsetInside
    rw [fields.2] at inside
    rw [fields.1]
    exact paths.pendingPending entry List.mem_cons_self nibbles length payload index inside current (List.mem_cons_of_mem entry inRest) owner slot occupied currentPayload offset offsetInside
  have newOwnerApart (active : heap≠0#64) : ∀ current∈rest,∀ pointer bytes,current.data.payload=.extension pointer bytes →
      ∀ index<bytes.toNat,∀ offset<TrieWalk.nodeBytes (wordAt post.memory heap),panByteAlignHOL (width:=64) (byteAddress pointer index)≠byteAddress heap offset:=by
    intro current inRest pointer bytes currentPayload index inside offset offsetInside
    have span:=pending current inRest
    simp only [currentPayload,WitnessRecord.Payload.PathBytes] at span
    have before:=(view.before current (List.mem_cons_of_mem entry inRest)).2.trans (view.marks current (List.mem_cons_of_mem entry inRest))
    simp only [currentPayload,WitnessRecord.Payload.endAddress] at before
    rw [tag] at offsetInside
    exact span.1.apart_before post.memory post.memaddrs post.be pointer heap bytes.toNat 56 extensionView.arena before index inside offset offsetInside
  have finalPaths : finalRegistry.PathModel:=oldPaths.registered post frontier db heap _ _ oldRegistry finalRegistry nodesPaths currentMembers
    (fun current inRest=>⟨current,inRest,rfl⟩) newPathApart newOwnerApart
  exact ⟨finalRegistry,finalPaths⟩

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.extension_paths_normal
