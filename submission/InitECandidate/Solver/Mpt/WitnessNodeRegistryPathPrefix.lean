import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real fresh allocation/copy preserves every older path's complete
backing word below the old heap, then permits increasing the heap bound. -/
theorem NodeRegistry.PathModel.prefix_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap nextHeap db : BitVec 64)
    (registry : NodeRegistry source frontier heap db) (next : NodeRegistry target frontier nextHeap db)
    (paths : registry.PathModel) (validEq : next.graph.valid=registry.graph.valid)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be) (grows : heap.toNat≤nextHeap.toNat)
    (memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) : next.PathModel := by
  have agree : ∀ query,registry.graph.Footprint query → target.memory query=source.memory query:=by
    intro query required
    exact memory query (registry.graph.footprint_bounds frontier heap.toNat registry.regions query required).2
  have bytes : ∀ node,registry.graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        target.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.bytes.span node member active tag
    have before:=(paths.regions node member active tag).2
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    apply memory
    rw [AllocatedBytes.aligned_number,number]
    omega
  exact ⟨paths.bytes.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be registry.graph next.graph validEq domain endian agree bytes,
    (paths.regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph frontier heap.toNat validEq agree).weaken
      next.graph frontier heap.toNat frontier nextHeap.toNat (Nat.le_refl _) grows,
    paths.separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs registry.graph next.graph validEq agree⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.prefix_frame
