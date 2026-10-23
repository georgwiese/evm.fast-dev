import InitECandidate.Solver.Mpt.CollapseBranchConcatEntry
import InitECandidate.Solver.Mpt.CollapseBranchConstructor

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete original concatenating collapse returns the real fresh
constructor result. Its registry is exactly the old registry plus that
result; copied buffers introduce no nodes. All older memory is retained. -/
theorem merge_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nibble child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (buffer : graph.PathBuffer source.be pathLower heap.toNat nibble 1) (floor : 2701131776≤pathLower) (nodeFloor : nodeLower≤heap.toNat)
    (member : graph.valid child) (active : child≠0#64) (tag : wordAt source.memory child=1#64 ∨ wordAt source.memory child=2#64)
    (nibbleCell : source.locals.lookup (ofString "nib")=some (.val (.word nibble)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source concatScope=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧
      source.clock-target.clock≤(wordAt source.memory (child+40#64)).toNat/8+22 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤root.toNat ∧ root.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,next.valid node ↔ graph.valid node ∨ node=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated := by
  obtain ⟨ready,inner,localsEq,readyDomain,readyEndian,readyCode,copyPrice,continued,endpoint,nextHeapCell,nextArena,nextAligned,grows,older,
    current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,joined⟩:=
    concat_entry source target heap nibble child graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated buffer floor member active tag
      nibbleCell childCell heapCell frontier aligned little domain installed value normal
  let childLength:=wordAt source.memory (child+40#64)
  let nextHeap:=PersistentAlloc.rounded heap (1#64+childLength)
  change heap.toNat+1+childLength.toNat≤nextHeap.toNat at grows
  change source.clock-ready.clock≤childLength.toNat/8+19 at copyPrice
  have childBefore : child.toNat<heap.toNat:=by
    have before:=(regions child member active).2.2.2
    have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory child)
    omega
  have fieldBefore : (child+40#64).toNat<heap.toNat:=by
    have inside : 40<TrieWalk.nodeBytes (wordAt source.memory child):=by rcases tag with tag|tag <;> rw [tag] <;> decide
    simpa only [byteAddress] using (graph.region_query_bounds nodeLower heap.toNat regions child 40 member active inside).2
  have currentTag : wordAt ready.memory child=wordAt source.memory child:=congrArg MemoryBytes.wordBits (older child childBefore)
  have currentLength : wordAt ready.memory (child+40#64)=wordAt source.memory (child+40#64):=congrArg MemoryBytes.wordBits (older _ fieldBefore)
  have currentKey : ready.locals.lookup (ofString "cat")=some (.val (.word heap)):=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
  have currentChild : ready.locals.lookup (ofString "child")=some (.val (.word child)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "cat"≠ofString "child" from by decide] using childCell
  have currentKind : ready.locals.lookup (ofString "ck")=some (.val (.word (wordAt ready.memory child))):=by
    rw [localsEq,currentTag]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "cat"≠ofString "ck" from by decide] using tagCell
  have currentMember : current.valid child:=by rw [same]; exact member
  have pathTag : wordAt ready.memory child=1#64 ∨ wordAt ready.memory child=2#64:=by rw [currentTag]; exact tag
  have currentBuffer : current.PathBuffer ready.be pathLower nextHeap.toNat heap (1+(wordAt ready.memory (child+40#64)).toNat):=by rw [currentLength]; exact joined
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [readyCode]; exact installed
  obtain ⟨answer,innerDomain,innerEndian,innerCode,price,innerMemory,finalHeap,finalCell,finalArena,finalAligned,heapGrows,
    next,members,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩:=
    constructor_paths ready inner nextHeap child heap current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated currentBuffer
      (by omega) currentMember active pathTag currentKey currentChild currentKind nextHeapCell nextArena nextAligned (readyDomain.trans domain) currentInstalled value continued
  have finalPrice : source.clock-inner.clock≤childLength.toNat/8+22:=by omega
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=
    (innerMemory query (by omega)).trans (older query before)
  have exactMembers (node : BitVec 64) : next.valid node ↔ graph.valid node ∨ node=nextHeap:=by rw [members node,same]
  rw [endpoint]
  exact ⟨innerDomain.trans readyDomain,innerEndian.trans readyEndian,innerCode.trans readyCode,finalPrice,memory,nextHeap,finalHeap,answer,finalCell,finalArena,finalAligned,
    by omega,heapGrows,next,exactMembers,root,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.merge_paths
