import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix
import InitECandidate.Solver.Mpt.WitnessDecodeSuffixCost
import InitECandidate.Solver.Mpt.WitnessMaterializeOutputAdvance
import InitECandidate.Solver.Mpt.NodeRegistryCopy32
import InitECandidate.Solver.WitnessRadix.AllocationContinuing

namespace InitECandidate.Solver.Mpt.WitnessDecodeRoot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open WitnessCore WitnessCore.Stack WitnessMaterialize Input.Main.RunAttemptConstructors

/-- The genuine root cache allocation/copy/store retains the materialized
closed graph and frozen databases, deriving actual room and next heap
from the real allocator. Normal copy writes supply their own footprint;
no source-buffer ownership is required. -/
theorem cache_allocated_normal_prefix (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap hashPtr node : BitVec 64)
    (output : RichOutput input frontier db source (.val (.word node))) (frontierLower : 2713731432≤frontier)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (nonnull : node≠0#64)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) 
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) : RichOutput input frontier db post (.val (.word node)) ∧ StablePrefix source post frontier := by
  have physical:=output.1
  obtain ⟨actualHeap,child,valueEq,actualCell,heapArena,heapAligned,frontierBefore,sourceScratch,frozen,owned⟩:=physical
  have sameHeap : actualHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  have sameChild : child=node := HolWordLab.word.inj (ValueHOL.val.inj valueEq.symm)
  subst child
  have nodeOwned:=owned.resolve_left nonnull
  have heapLower : 2713731432≤heap.toNat := frontierLower.trans frontierBefore
  have heapNonzero : heap≠0#64 := by intro zero; rw [zero] at heapLower; change 2713731432≤0 at heapLower; omega
  obtain ⟨codeArray,nodes,codes,nodeData,codeData,dbCell,nodeBefore,codeBefore⟩:=frozen
  have sourceDomain : source.memaddrs=InitE.ordinaryDomain := nodeData.domain
  obtain ⟨modelHeap,modelChild,modelValue,modelCell,registry,member⟩:=output.2
  have modelHeapEq : modelHeap=heap := HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (modelCell.symm.trans heapCell)))
  subst modelHeap
  have modelChildEq : modelChild=node := HolWordLab.word.inj (ValueHOL.val.inj modelValue.symm)
  subst modelChild
  rw [cacheAllocated] at normal
  obtain ⟨room,funded,inner,continued,postEq⟩:=PersistentAlloc.call_continuing source post "h" [.const 32#64] (.seq rootCopy rootCache) heap 32#64 rfl
    (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed) heapCell (by have upper:=heapArena.upper; omega) normal
  let ready:=QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap 32#64) "h" heap
  let next:=PersistentAlloc.rounded heap 32#64
  have checked:=PersistentAlloc.guards heap 32#64 room
  have grows : heap.toNat≤next.toNat := by have bound:=checked.2.2.1; change heap.toNat+32≤next.toNat at bound; omega
  have nextArena : AllocatedBytes.Arena next 0 := ⟨by have lower:=heapArena.lower; omega,by have upper:=checked.2.2.2.1; change next.toNat≤33806089496 at upper; omega⟩
  have targetArena : AllocatedBytes.Arena heap 32 := ⟨heapArena.lower,room⟩
  have readyHash : ready.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)) :=
    (bind_lookup_other _ "h" "root_hash" heap (by decide)).trans hashCell
  have readyNode : ready.locals.lookup (ofString "nd")=some (.val (.word node)) := (bind_lookup_other _ "h" "nd" heap (by decide)).trans nodeCell
  have readyH : ready.locals.lookup (ofString "h")=some (.val (.word heap)) := bind_lookup_same _ _ _
  have args : evalListHOLFinite ready (h:=fun address=>Classical.propDecidable (ready.memaddrs address))
      [localVar "h",localVar "root_hash",.const 32#64]=some (CopyGeneral.values heap hashPtr 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,readyH,readyHash,CopyGeneral.values]
  obtain ⟨copied,copyRun,cacheRun⟩:=Input.sequence_none ready inner rootCopy rootCache continued
  obtain ⟨readyRegistry,readyValid⟩:=registry.of_fields source ready frontier heap db rfl rfl
  obtain ⟨⟨copiedRegistry,copiedValid⟩,copyMemory⟩:=readyRegistry.copy32_after ready copied frontier heap db hashPtr heap _ (Nat.le_refl _) targetArena heapAligned
    installed args copyRun
  obtain ⟨copiedFrame,copiedLocals⟩:=Input.Copy32Span.call_normal ready copied heap hashPtr _ args installed copyRun
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
  have copiedMember : copiedRegistry.graph.valid node := by rw [copiedValid,readyValid]; exact member
  let expanded:=copiedRegistry.advance_heap copied frontier heap next db grows
  obtain ⟨cachedRegistry,cachedValid⟩:=expanded.after_cache copied frontier next db node heap copiedMember
  have postMemory : post.memory=cached.memory := by rw [postEq,innerEq]; rfl
  have postDomain : post.memaddrs=cached.memaddrs := by rw [postEq,innerEq]; rfl
  obtain ⟨postRegistry,postValid⟩:=cachedRegistry.of_fields cached post frontier next db postMemory postDomain
  have postMember : postRegistry.graph.valid node := by rw [postValid,cachedValid]; exact copiedMember
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
  have memory : ∀ query : BitVec 64,2713717616≤query.toNat → query.toNat<frontier → post.memory query=source.memory query := by
    intro query lower upper
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
  refine ⟨output.advance_frame input frontier db heap next node source post (.val (.word node)) rfl heapCell targetHeap nextArena checked.2.2.2.2 grows
    domain endian scratch memory kind postRegistry postMember,memory⟩

theorem cache_allocated_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap hashPtr node : BitVec 64)
    (output : RichOutput input frontier db source (.val (.word node))) (frontierLower : 2713731432≤frontier)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) (nonnull : node≠0#64)
    (hashCell : source.locals.lookup (ofString "root_hash")=some (.val (.word hashPtr)))
    (nodeCell : source.locals.lookup (ofString "nd")=some (.val (.word node))) 
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source cacheAllocated=(none,post)) : RichOutput input frontier db post (.val (.word node)) :=
  (cache_allocated_normal_prefix input source post frontier db heap hashPtr node output frontierLower heapCell nonnull hashCell nodeCell installed normal).1

end InitECandidate.Solver.Mpt.WitnessDecodeRoot

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_allocated_normal

#print axioms InitECandidate.Solver.Mpt.WitnessDecodeRoot.cache_allocated_normal_prefix
