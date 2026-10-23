import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real older workspace word lies below every node and every path
backing word. The eight-byte gap also covers unaligned path pointers. -/
theorem NodeRegistry.PathModel.store_below (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db address value : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (next : NodeRegistry {source with memory:=StoreWord.put source.memory address value} frontier heap db)
    (paths : registry.PathModel) (validEq : next.graph.valid=registry.graph.valid) (before : address.toNat+8≤frontier) : next.PathModel := by
  let post : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory address value}
  have agree : ∀ query,registry.graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have lower:=(registry.graph.footprint_bounds frontier heap.toNat registry.regions query required).1
    have away : query≠address:=by intro same; have number:=congrArg BitVec.toNat same; omega
    exact if_neg away
  have bytes : ∀ node,registry.graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.bytes.span node member active tag
    have lower:=(paths.regions node member active tag).1
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    have away : panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)≠address:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      rw [AllocatedBytes.aligned_number,number] at numeric
      omega
    exact if_neg away
  exact ⟨paths.bytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be registry.graph next.graph validEq rfl rfl agree bytes,
    paths.regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph frontier heap.toNat validEq agree,
    paths.separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph validEq agree⟩

/-- A word in a genuinely newer allocation is above all old node and
path extents, so even their final backing words remain untouched. -/
theorem NodeRegistry.PathModel.store_above (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db address value : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (next : NodeRegistry {source with memory:=StoreWord.put source.memory address value} frontier heap db)
    (paths : registry.PathModel) (validEq : next.graph.valid=registry.graph.valid) (after : heap.toNat≤address.toNat) : next.PathModel := by
  let post : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory address value}
  have agree : ∀ query,registry.graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have upper:=(registry.graph.footprint_bounds frontier heap.toNat registry.regions query required).2
    have away : query≠address:=by intro same; have number:=congrArg BitVec.toNat same; omega
    exact if_neg away
  have bytes : ∀ node,registry.graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.bytes.span node member active tag
    have upper:=(paths.regions node member active tag).2
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    have away : panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)≠address:=by
      intro same
      have numeric:=congrArg BitVec.toNat same
      rw [AllocatedBytes.aligned_number,number] at numeric
      omega
    exact if_neg away
  exact ⟨paths.bytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be registry.graph next.graph validEq rfl rfl agree bytes,
    paths.regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph frontier heap.toNat validEq agree,
    paths.separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs registry.graph next.graph validEq agree⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.store_below
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.store_above
