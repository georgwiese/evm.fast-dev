import InitECandidate.Solver.Mpt.CollapseBranchNibbleAllocation
import InitECandidate.Solver.Mpt.CollapseBranchAfterStoreNormal

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original nib scope: actual eight-byte allocation, byte store,
branch or full-path merge, constructor and lexical exit. Exactly the
returned fresh node is added, and every older memory word is retained. -/
theorem nibble_paths (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap index child : BitVec 64)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (lower : pathLower≤heap.toNat) (floor : 2701131776≤pathLower) (nodeFloor : nodeLower≤heap.toNat)
    (bounded : index.toNat<16) (member : graph.valid child) (active : child≠0#64) (notHash : wordAt source.memory child≠0#64)
    (indexCell : source.locals.lookup (ofString "idx")=some (.val (.word index)))
    (childCell : source.locals.lookup (ofString "child")=some (.val (.word child)))
    (tagCell : source.locals.lookup (ofString "ck")=some (.val (.word (wordAt source.memory child))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (little : source.be=false) (domain : source.memaddrs=InitE.ordinaryDomain) (installed : Input.OriginalCode.Installed source.code)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source nibbleScope=(some (.returned value),target)) :
    target.memaddrs=source.memaddrs ∧ target.be=source.be ∧ target.code=source.code ∧ source.clock-target.clock≤afterStorePrice source.memory child+1 ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) ∧
      ∃ root finalHeap : BitVec 64,value=.val (.word root) ∧ target.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧
        AllocatedBytes.Arena finalHeap 0 ∧ finalHeap.toNat%8=0 ∧ heap.toNat≤root.toNat ∧ root.toNat≤finalHeap.toNat ∧
        ∃ next : TrieWalk.Graph target.memory target.memaddrs,(∀ node,next.valid node ↔ graph.valid node ∨ node=root) ∧ next.valid root ∧
          next.Regions nodeLower finalHeap.toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
          next.PathBytes target.be ∧ next.PathRegions pathLower finalHeap.toNat ∧ next.PathSeparated ∧
          (∀ address : BitVec 64,graph.ProtectedWord address → address.toNat<heap.toNat → next.ProtectedWord address) := by
  obtain ⟨ready,inner,localsEq,readyDomain,readyEndian,readyCode,entryPrice,nextHeapCell,nextArena,nextAligned,grows,continued,endpoint,older,
    current,same,currentRegions,currentDisjoint,⟨currentValues⟩,currentPaths,currentPathRegions,currentSeparated,buffer⟩:=
    nibble_entry_paths source target heap index graph limit nodeLower pathLower property values regions disjoint paths pathRegions separated lower bounded indexCell heapCell frontier aligned little domain installed value normal
  let nextHeap:=PersistentAlloc.rounded heap 8#64
  change heap.toNat+8≤nextHeap.toNat at grows
  have childBefore : child.toNat<heap.toNat:=by
    have before:=(regions child member active).2.2.2
    have size:=TrieWalk.nodeBytes_bounds (wordAt source.memory child)
    omega
  have inside : 40<TrieWalk.nodeBytes (wordAt source.memory child):=by
    rcases (graph.kind_cases child member active).resolve_left notHash with one|two|three
    · rw [one]; decide
    · rw [two]; decide
    · rw [three]; decide
  have fieldBefore : (child+40#64).toNat<heap.toNat:=by
    simpa only [byteAddress] using (graph.region_query_bounds nodeLower heap.toNat regions child 40 member active inside).2
  have currentTag : wordAt ready.memory child=wordAt source.memory child:=congrArg MemoryBytes.wordBits (older child childBefore)
  have currentLength : wordAt ready.memory (child+40#64)=wordAt source.memory (child+40#64):=congrArg MemoryBytes.wordBits (older _ fieldBefore)
  have currentNibble : ready.locals.lookup (ofString "nib")=some (.val (.word heap)):=by rw [localsEq]; simp [HolFiniteMapExact.update,FUPDATE]
  have currentChild : ready.locals.lookup (ofString "child")=some (.val (.word child)):=by
    rw [localsEq]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "nib"≠ofString "child" from by decide] using childCell
  have currentKind : ready.locals.lookup (ofString "ck")=some (.val (.word (wordAt ready.memory child))):=by
    rw [localsEq,currentTag]
    simpa [HolFiniteMapExact.update,FUPDATE,show ofString "nib"≠ofString "ck" from by decide] using tagCell
  have currentMember : current.valid child:=by rw [same]; exact member
  have currentNotHash : wordAt ready.memory child≠0#64:=by rwa [currentTag]
  have currentInstalled : Input.OriginalCode.Installed ready.code:=by rw [readyCode]; exact installed
  obtain ⟨domainEq,endianEq,codeEq,price,innerMemory,root,finalHeap,answer,finalCell,finalArena,finalAligned,fresh,heapGrows,
    next,members,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,tailProtection⟩:=
    after_store_paths ready inner nextHeap heap child current limit nodeLower pathLower property currentValues currentRegions currentDisjoint currentPaths currentPathRegions currentSeparated buffer floor
      (by omega) currentMember active currentNotHash currentNibble currentChild currentKind nextHeapCell nextArena nextAligned (readyEndian.trans little) (readyDomain.trans domain) currentInstalled value continued
  have samePrice : afterStorePrice ready.memory child=afterStorePrice source.memory child:=by simp only [afterStorePrice,currentTag,currentLength]
  rw [samePrice] at price
  have finalPrice : source.clock-inner.clock≤afterStorePrice source.memory child+1:=by omega
  have memory (query : BitVec 64) (before : query.toNat<heap.toNat) : inner.memory query=source.memory query:=
    (innerMemory query (by omega)).trans (older query before)
  have exactMembers (node : BitVec 64) : next.valid node ↔ graph.valid node ∨ node=root:=by rw [members node,same]
  have protection (address : BitVec 64) (safe : graph.ProtectedWord address) (before : address.toNat<heap.toNat) : next.ProtectedWord address:=by
    have oldFields:=TrieWalk.Graph.PathFields.of_prefix graph ready.memory nodeLower heap.toNat regions older
    have currentSafe:=safe.of_fields graph current address same oldFields
    have away:=TrieWalk.PathWordAway.above_frontier heap address 1 heap.toNat buffer.span.fits aligned before (Nat.le_refl _)
    exact tailProtection address currentSafe (by omega) away
  rw [endpoint]
  exact ⟨domainEq.trans readyDomain,endianEq.trans readyEndian,codeEq.trans readyCode,finalPrice,memory,root,finalHeap,answer,finalCell,finalArena,finalAligned,
    by omega,heapGrows,next,exactMembers,rootMember,nextRegions,nextDisjoint,nextValues,nextPaths,nextPathRegions,nextSeparated,protection⟩

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.nibble_paths
