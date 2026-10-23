import InitECandidate.Solver.Mpt.WitnessRegistryJoin
import InitECandidate.Solver.Mpt.TrieGraphPathUnion
import InitECandidate.Solver.Mpt.WitnessMaterializePathOutput

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessCore WitnessCore.Stack

/-- Join the actual newly decoded path registry with every live caller
node/path. Source prefix protection and the real aligned heap frontier
establish all bytes and both cross-allocation separation directions. -/
theorem PathOutput.join_registry_paths (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap : BitVec 64) (returned : ValueHOL 64) (lower pathLower limit : Nat)
    (output : PathOutput input heap.toNat db post returned) (memory : StablePrefix source post heap.toNat)
    (domain : post.memaddrs=source.memaddrs) (endian : post.be=source.be) (old : TrieWalk.Graph source.memory source.memaddrs)
    (property : BitVec 64 → BitVec 64 → Prop) (oldValues : TrieWalk.Values old limit property)
    (oldRegions : old.Regions lower heap.toNat) (oldDisjoint : old.Disjoint)
    (oldBytes : old.PathBytes source.be) (oldPaths : old.PathRegions pathLower heap.toNat) (oldSeparated : old.PathSeparated)
    (pathFloor : 2713717616+7≤pathLower) (pathOrdered : pathLower≤heap.toNat) (heapAligned : heap.toNat%8=0)
    (floor : 2713717616≤lower) (ordered : lower≤heap.toNat) (bounded : 1024≤limit)
    (extra : ∀ pointer length,WitnessValue db pointer length → property pointer length) :
    ∃ nextHeap node,returned=.val (.word node) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      ∃ graph : TrieWalk.Graph post.memory post.memaddrs,
        Nonempty (TrieWalk.Values graph limit property) ∧ graph.Regions lower nextHeap.toNat ∧ graph.Disjoint ∧
        graph.PathBytes post.be ∧ graph.PathRegions pathLower nextHeap.toNat ∧ graph.PathSeparated ∧
        (∀ child,old.valid child → graph.valid child) ∧ graph.valid node := by
  obtain ⟨kept,same,keptRegions,keptDisjoint,⟨keptValues⟩⟩:=old.after_agreement source post limit lower heap.toNat property oldValues oldRegions oldDisjoint domain
    (by intro query needed; have bounds:=old.footprint_bounds lower heap.toNat oldRegions query needed; exact memory query (floor.trans bounds.1) bounds.2)
    (by intro query needed; have bounds:=old.value_bounds lower heap.toNat oldRegions query needed; exact memory query (floor.trans bounds.1) bounds.2)
  have agree : ∀ query,old.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have bounds:=old.footprint_bounds lower heap.toNat oldRegions query required
    exact memory query (floor.trans bounds.1) bounds.2
  have bytes : ∀ node,old.valid node → node≠0#64 → (GasBudget.wordAt source.memory node=1#64 ∨ GasBudget.wordAt source.memory node=2#64) →
      ∀ index<(GasBudget.wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (GasBudget.wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (GasBudget.wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=oldBytes.span node member active tag
    have bounds:=oldPaths node member active tag
    have number:=byteAddress_toNat (GasBudget.wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    apply memory
    · rw [AllocatedBytes.aligned_number,number]
      omega
    · rw [AllocatedBytes.aligned_number,number]
      omega
  have keptBytes:=oldBytes.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be old kept same domain endian agree bytes
  have keptPaths:=oldPaths.of_agreement source.memory post.memory source.memaddrs post.memaddrs old kept pathLower heap.toNat same agree
  have keptSeparated:=oldSeparated.of_agreement source.memory post.memory source.memaddrs post.memaddrs old kept same agree
  obtain ⟨actualHeap,child,valueEq,heapCell,registry,registryPaths,member⟩:=output.2
  have physical:=output.1
  obtain ⟨physicalHeap,physicalChild,physicalValue,physicalCell,arena,aligned,grows,rest⟩:=physical
  have sameHeap : physicalHeap=actualHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (physicalCell.symm.trans heapCell)))
  subst physicalHeap
  let graph:=kept.union registry.graph
  have freshValues : TrieWalk.Values registry.graph limit property:=
    (registry.values.map_extra post.memory post.memaddrs registry.graph 1024 (WitnessValue db) property extra).widen bounded
  refine ⟨actualHeap,child,valueEq,heapCell,graph,⟨TrieWalk.Values.union kept registry.graph limit property keptValues freshValues⟩,
    keptRegions.union kept registry.graph lower heap.toNat actualHeap.toNat registry.regions ordered grows,
    keptDisjoint.union kept registry.graph lower heap.toNat actualHeap.toNat keptRegions registry.regions registry.disjoint,
    keptBytes.union kept registry.graph post.be registryPaths.bytes,
    keptPaths.union kept registry.graph pathLower heap.toNat actualHeap.toNat registryPaths.regions pathOrdered grows,
    keptSeparated.union kept registry.graph post.be lower pathLower heap.toNat actualHeap.toNat keptRegions registry.regions keptPaths registryPaths.regions keptBytes registryPaths.bytes registryPaths.separated heapAligned,
    ?_,Or.inr member⟩
  intro child known
  exact Or.inl (by rw [same]; exact known)

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.PathOutput.join_registry_paths
