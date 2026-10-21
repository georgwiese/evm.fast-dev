import InitECandidate.Solver.Mpt.WitnessCoreRichInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- An actual word store outside all live node allocations retains their
closed structure, bounded values, exact membership and disjoint extents. -/
theorem NodeRegistry.store_outside (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db address value : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (outside : address.toNat<frontier ∨ heap.toNat≤address.toNat) :
    ∃ next : NodeRegistry {source with memory:=StoreWord.put source.memory address value} frontier heap db,
      next.graph.valid=registry.graph.valid := by
  let target : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory address value}
  have agree (query : BitVec 64) (above : frontier≤query.toNat) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=by
    have away : query≠address:=by intro equal; subst query; omega
    exact if_neg away
  obtain ⟨graph,same,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint rfl
    (fun query needed=>agree query (registry.graph.footprint_bounds frontier heap.toNat registry.regions query needed).1
      (registry.graph.footprint_bounds frontier heap.toNat registry.regions query needed).2)
    (fun query needed=>agree query (registry.graph.value_bounds frontier heap.toNat registry.regions query needed).1
      (registry.graph.value_bounds frontier heap.toNat registry.regions query needed).2)
  exact ⟨⟨graph,values,regions,disjoint⟩,same⟩

theorem NodeRegistry.store_below (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db address value : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (below : address.toNat<frontier) :
    ∃ next : NodeRegistry {source with memory:=StoreWord.put source.memory address value} frontier heap db,
      next.graph.valid=registry.graph.valid :=
  registry.store_outside source frontier heap db address value (Or.inl below)

theorem NodeRegistry.store_above (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db address value : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (above : heap.toNat≤address.toNat) :
    ∃ next : NodeRegistry {source with memory:=StoreWord.put source.memory address value} frontier heap db,
      next.graph.valid=registry.graph.valid :=
  registry.store_outside source frontier heap db address value (Or.inr above)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.store_below
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.store_above
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.store_outside
