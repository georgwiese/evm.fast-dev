import InitECandidate.Solver.Mpt.WitnessCoreRichInvariant
import InitECandidate.Solver.MutableTable.TableRuntime.Frames

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix MutableTable MutableTable.NaturalLayout

/-- The genuine table constructor's exact memory writes are all in its
fresh reservation. Every live trie node and value word below that real
incoming heap survives, at the actual advanced heap cursor. -/
theorem NodeRegistry.table_new (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (heap db : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (name : String) (kind : KeyHash.Kind) (start capacity : Nat)
    (heapNumber : heap.toNat=start) (valid : Valid kind (fresh kind start capacity)) :
    ∃ next : NodeRegistry (TableRuntime.callState source name kind start capacity) frontier (BitVec.ofNat 64 (freshEnd kind start capacity)) db,
      next.graph.valid=registry.graph.valid := by
  let target:=TableRuntime.callState source name kind start capacity
  have agree (query : BitVec 64) (before : query.toNat<heap.toNat) : target.memory query=source.memory query:=
    TableRuntime.caller_memory_away source name kind start capacity valid query (Or.inl (by rwa [←heapNumber]))
  obtain ⟨graph,same,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint rfl
    (fun query needed=>agree query (registry.graph.footprint_bounds frontier heap.toNat registry.regions query needed).2)
    (fun query needed=>agree query (registry.graph.value_bounds frontier heap.toNat registry.regions query needed).2)
  have endBound : freshEnd kind start capacity≤33806089496:=by
    have upper:=valid.upper .position
    simpa only [fresh,size,freshEnd] using upper
  have endNumber : (BitVec.ofNat 64 (freshEnd kind start capacity)).toNat=freshEnd kind start capacity:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have grows : heap.toNat≤(BitVec.ofNat 64 (freshEnd kind start capacity)).toNat:=by
    rw [heapNumber,endNumber,freshEnd]; omega
  exact ⟨⟨graph,values,regions.weaken graph frontier heap.toNat frontier _ (Nat.le_refl _) grows,disjoint⟩,same⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.table_new
