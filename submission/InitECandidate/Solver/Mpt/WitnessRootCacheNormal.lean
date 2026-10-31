import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix
import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost
import InitECandidate.Solver.Mpt.WitnessMaterializeOutputAdvance
import InitECandidate.Solver.Input.Copy32SpanCall
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals
import InitECandidate.Solver.WitnessRadix.AllocationContinuing

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack WitnessMaterialize Input.Main.RunAttemptConstructors

/-- The real root-cache allocation, copy and node store retain the current
Patricia database and earlier memory. Exact room and next heap follow from
the observed allocator; the actual copy supplies its own write footprint. -/
theorem cache_allocated_normal_prefix (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap hashPtr node : BitVec 64)
    (output : Output data frontier db source (.val (.word node)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (nonnull : node≠0#64)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) 
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) : Output data frontier db post (.val (.word node)) ∧ StablePrefix source post frontier ∧
      (∀ key,key≠ofString "heap_ptr"→post.globals.lookup key=source.globals.lookup key) := by
  have physical:=output
  obtain ⟨actualHeap,child,valueEq,actualCell,heapArena,heapBound,heapAligned,frontierBefore,sourceScratch,tableBefore,database,owned⟩:=physical
  have sameHeap : actualHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have sameChild : child=node := HolWordLab.word.inj (ValueHOL.val.inj valueEq.symm)
  subst child
  have nodeOwned:=owned.resolve_left nonnull
  have heapNonzero : heap≠0#64 := by
    intro zero
    have lower:=heapArena.lower
    rw [zero] at lower
    change 2701131776≤0 at lower
    omega
  have sourceDomain : source.memaddrs=InitE.ordinaryDomain:=by
    obtain ⟨imageRoot,nextNode,count,valid,bits,left,right,keys,image,bounded⟩:=database.image
    exact image.domain
  rw [cacheAllocated] at normal
  obtain ⟨room,funded,inner,continued,postEq⟩:=PersistentAlloc.call_continuing source post "h" [.const 32#64] (.seq rootCopy rootCache) heap 32#64 rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell heapBound normal
  let ready:=QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
  let next:=PersistentAlloc.rounded heap 32#64
  have checked:=PersistentAlloc.guards heap 32#64 room
  have grows : heap.toNat≤next.toNat := by have bound:=checked.2.2.1; change heap.toNat+32≤next.toNat at bound; omega
  have nextArena : AllocatedBytes.Arena next 0 := ⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; change next.toNat≤2952790016 at upper; omega⟩
  have targetArena : AllocatedBytes.Arena heap 32 := ⟨heapArena.lower,by omega⟩
  have readyHash : ready.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)) :=
    (bind_lookup_other _ "h" "root_hash" heap (by decide)).trans hashCell
  have readyNode : ready.locals.lookup (ofString "nd")=some (.val (.word node)) := (bind_lookup_other _ "h" "nd" heap (by decide)).trans nodeCell
  have readyH : ready.locals.lookup (ofString "h")=some (.val (.word heap)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address))
      [localVar "h",localVar "root_hash",.const 32#64]=some (CopyGeneral.values heap hashPtr 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,readyH,readyHash,CopyGeneral.values]
  obtain ⟨copied,copyRun,cacheRun⟩:=Input.sequence_none ready inner rootCopy rootCache continued
  obtain ⟨copiedFrame,copiedLocals⟩:=Input.Copy32Span.call_normal ready copied heap hashPtr _ args installed copyRun
  have copyMemory (query : BitVec 64) (earlier : query.toNat<heap.toNat) : copied.memory query=source.memory query:=
    copiedFrame.memory query (CopyGeneral.Away.after heap query 32 heapAligned (by have upper:=targetArena.upper; omega) earlier)
  have copiedNode : copied.locals.lookup (ofString "nd")=some (.val (.word node)):=by rw [copiedLocals]; exact readyNode
  have copiedH : copied.locals.lookup (ofString "h")=some (.val (.word heap)):=by rw [copiedLocals]; exact readyH
  have copiedDomain : copied.memaddrs=source.memaddrs:=copiedFrame.domain
  have mapped : copied.memaddrs (node+24#64) := AllocatedBytes.word_mapped copied node 32 24 (copiedDomain.trans sourceDomain) nodeOwned.arena (by decide) nodeOwned.aligned (by decide)
  have addressRead : eval copied (addConst (localVar "nd") 24#64)=some (.val (.word (node+24#64))) := by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,copiedNode,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval copied (localVar "h")=some (.val (.word heap)) := by simp [eval,localVar,evalHOLExact,toExact,copiedH]
  let stored : PanSemStateFiniteExact 64 Guest.HostMemory:={copied with memory:=StoreWord.put copied.memory (node+24#64) heap}
  have storeRun : evaluateHOLFiniteState copied rootCache=(none,stored) := StoreWord.execute copied _ _ (node+24#64) heap addressRead valueRead mapped
  have innerStored : inner=stored := congrArg Prod.snd (cacheRun.symm.trans storeRun)
  let cached:=returnCacheState copied node heap
  have cacheEq : cached=stored := by simp only [cached,returnCacheState,heapNonzero,nonnull,or_self,↓reduceIte]; rfl
  have innerEq : inner=cached := innerStored.trans cacheEq.symm
  have postMemory : post.memory=cached.memory := by rw [postEq,innerEq]; rfl
  have postDomain : post.memaddrs=cached.memaddrs := by rw [postEq,innerEq]; rfl
  have postGlobals : post.globals=ready.globals := by
    rw [postEq,innerEq,cacheEq]
    change copied.globals=ready.globals
    exact copiedFrame.globals
  have targetHeap : post.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) := by
    rw [postGlobals]
    simp [ready,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,next]
  have scratch : ∃ cursor,post.globals.lookup (ofString "scratch_ptr")=some (.val (.word cursor)) := by
    obtain ⟨cursor,cell⟩:=sourceScratch
    refine ⟨cursor,?_⟩
    rw [postGlobals]
    simpa [ready,PersistentAlloc.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using cell
  have domain : post.memaddrs=source.memaddrs := by
    rw [postEq,innerEq,cacheEq]
    exact copiedDomain
  have endian : post.be=source.be := by
    rw [postEq,innerEq,cacheEq]
    change copied.be=source.be
    exact copiedFrame.endian
  have cacheNumber : (node+24#64).toNat=node.toNat+24 := byteAddress_toNat node 24 (by have upper:=nodeOwned.arena.upper; omega)
  have memory : ∀ query : BitVec 64,query.toNat<frontier → post.memory query=source.memory query := by
    intro query upper
    rw [postMemory]
    have away : query≠node+24#64 := by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [cacheNumber] at numeric; have fresh:=nodeOwned.fresh; omega
    exact (return_cache_memory copied node heap query away).trans (copyMemory query (upper.trans_le frontierBefore))
  have kind : node≠0#64 → post.memory node=source.memory node := by
    intro active
    rw [postMemory]
    have away : node≠node+24#64 := by
      intro equal
      have impossible : (0#64 : BitVec 64)=24#64 := (BitVec.add_right_inj node).mp (by simpa only [BitVec.add_zero] using equal)
      exact (by decide : (0#64 : BitVec 64)≠24#64) impossible
    exact (return_cache_memory copied node heap node away).trans (copyMemory node (by have before:=nodeOwned.before; omega))
  refine ⟨output.advance_frame data frontier db heap next node source post (.val (.word node)) rfl heapCell targetHeap nextArena checked.2.2.2.1 checked.2.2.2.2 grows
    domain endian scratch memory kind,memory,?_⟩
  intro key notHeap
  rw [postGlobals]
  change (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64).globals.lookup key=source.globals.lookup key
  simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]

theorem cache_allocated_normal (data : Input.CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap hashPtr node : BitVec 64)
    (output : Output data frontier db source (.val (.word node)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (nonnull : node≠0#64)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) 
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) : Output data frontier db post (.val (.word node)) :=
  (cache_allocated_normal_prefix data source post frontier db heap hashPtr node output heapCell nonnull hashCell nodeCell installed normal).1

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_allocated_normal

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_allocated_normal_prefix
