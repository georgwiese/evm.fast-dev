import InitECandidate.Solver.Mpt.WitnessCoreRichInvariant
import InitECandidate.Solver.Mpt.TriePathBytesRegister

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Actual full path bytes and their lifetimes in a completed witness
registry. The path backing words are separate from every mutable node. -/
structure NodeRegistry.PathModel {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frontier : Nat} {heap db : BitVec 64} (registry : NodeRegistry source frontier heap db) : Prop where
  bytes : registry.graph.PathBytes source.be
  regions : registry.graph.PathRegions frontier heap.toNat
  separated : registry.graph.PathSeparated

theorem NodeRegistry.PathModel.empty (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64) : (NodeRegistry.empty source frontier heap db).PathModel :=
  ⟨TrieWalk.Graph.PathBytes.empty source.memory source.memaddrs source.be,
    TrieWalk.Graph.PathRegions.empty source.memory source.memaddrs frontier heap.toNat,
    TrieWalk.Graph.PathSeparated.empty source.memory source.memaddrs⟩

/-- A genuine decoder frame protects the completed paths in its real
scratch-to-heap band, including each unaligned final backing word. -/
theorem NodeRegistry.PathModel.normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap nextHeap db cursor limit : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (next : NodeRegistry target frontier nextHeap db)
    (paths : registry.PathModel) (validEq : next.graph.valid=registry.graph.valid)
    (scratchBelow : cursor.toNat+7≤frontier) (grows : heap.toNat≤nextHeap.toNat)
    (frame : WitnessDecode.NormalFrame source target heap cursor limit) : next.PathModel := by
  have agree : ∀ query,registry.graph.Footprint query→target.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions query required
    exact frame.memory query (by omega) bounds.2
  have bytes : ∀ node,registry.graph.valid node→node≠0#64→(wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)→
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        target.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.bytes.span node member active tag
    have bounds:=paths.regions node member active tag
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    apply frame.memory
    · rw [AllocatedBytes.aligned_number,number]
      omega
    · rw [AllocatedBytes.aligned_number,number]
      omega
  exact ⟨paths.bytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be
      registry.graph next.graph validEq frame.domain frame.endian agree bytes,
    (paths.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph frontier heap.toNat validEq agree).weaken
      next.graph frontier heap.toNat frontier nextHeap.toNat (Nat.le_refl _) grows,
    paths.separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph validEq agree⟩

/-- The actual optional HASH24 update retains full path bytes because
their backing words are outside every mutable node allocation. -/
theorem NodeRegistry.PathModel.cache (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db child hash : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (paths : registry.PathModel) (member : registry.graph.valid child)
    (next : NodeRegistry (returnCacheState source child hash) frontier heap db)
    (validEq : next.graph.valid=registry.graph.valid) : next.PathModel := by
  let post:=returnCacheState source child hash
  have domain : post.memaddrs=source.memaddrs:=by unfold post returnCacheState; split <;> rfl
  have endian : post.be=source.be:=by unfold post returnCacheState; split <;> rfl
  by_cases zero : child=0#64
  · have memory : post.memory=source.memory:=by simp [post,returnCacheState,zero]
    have agree : ∀ query,registry.graph.Footprint query→post.memory query=source.memory query:=by intros; rw [memory]
    exact ⟨paths.bytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be registry.graph next.graph validEq domain endian agree (by intros; rw [memory]),
      paths.regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph frontier heap.toNat validEq agree,
      paths.separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph validEq agree⟩
  · have agree : ∀ query,registry.graph.Footprint query→post.memory query=source.memory query:=by
      intro query required
      obtain ⟨node,offset,nodeMember,active,inside,notCache,equal⟩:=required.location registry.graph query
      exact return_cache_memory source child hash query (by
        rw [equal]
        exact registry.graph.cache_away frontier heap.toNat registry.regions registry.disjoint child node offset member zero nodeMember active inside notCache)
    have bytes : ∀ node,registry.graph.valid node→node≠0#64→(wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)→
        ∀ index<(wordAt source.memory (node+40#64)).toNat,
          post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
          source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
      intro node nodeMember active tag index inside
      exact return_cache_memory source child hash _ (paths.separated node nodeMember active tag index inside child member zero 24
        (by have bounds:=TrieWalk.nodeBytes_bounds (wordAt source.memory child); omega))
    exact ⟨paths.bytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be registry.graph next.graph validEq domain endian agree bytes,
      paths.regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph frontier heap.toNat validEq agree,
      paths.separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph validEq agree⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.empty
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.normal_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.cache
