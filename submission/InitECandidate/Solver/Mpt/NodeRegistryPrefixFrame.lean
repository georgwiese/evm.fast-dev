import InitECandidate.Solver.Mpt.WitnessCoreRichInvariant

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A genuine older-word prefix frame retains every live node and value
field and permits advancing the actual heap bound. -/
theorem NodeRegistry.after_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap nextHeap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (domain : target.memaddrs=source.memaddrs) (grows : heap.toNat≤nextHeap.toNat)
    (memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) :
    ∃ next : NodeRegistry target frontier nextHeap db,next.graph.valid=registry.graph.valid := by
  obtain ⟨graph,same,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain
    (fun query needed=>memory query (registry.graph.footprint_bounds frontier heap.toNat registry.regions query needed).2)
    (fun query needed=>memory query (registry.graph.value_bounds frontier heap.toNat registry.regions query needed).2)
  exact ⟨⟨graph,values,regions.weaken graph frontier heap.toNat frontier nextHeap.toNat (Nat.le_refl _) grows,disjoint⟩,same⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.after_prefix
