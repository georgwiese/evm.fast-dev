import InitECandidate.Solver.Mpt.WitnessCoreRegistryConstructors

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The actual child/OCC/i prefix writes only the selected pending-node
slot and the scratch OCC word. Every disjoint completed node survives. -/
theorem branch_counter_outside_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17)
    (arena : AllocatedBytes.Arena node 176) (ceiling : record.toNat+88≤2713717616)
    (query : BitVec 64) (floor : 2713731432≤query.toNat) (outside : query.toNat<node.toNat ∨ node.toNat+176≤query.toNat) :
    (branchCounterEntry source record node child index occupied).memory query=source.memory query := by
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val) :=
    byteAddress_toNat node _ (by have upper:=arena.upper; have bound:=index.isLt; omega)
  have recordNumber : (record+40#64).toNat=record.toNat+40 := byteAddress_toNat record 40 (by omega)
  apply branch_counter_entry_memory source record node child index occupied query
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [childNumber] at numeric
    have bound:=index.isLt
    omega
  · intro equal
    have numeric:=congrArg BitVec.toNat equal
    rw [recordNumber] at numeric
    omega

theorem NodeRegistry.branch_counter (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17)
    (registry : NodeRegistry source frontier heap db) (frontierLower : 2713731432≤frontier)
    (excluded : registry.graph.Excludes node 176) (arena : AllocatedBytes.Arena node 176)
    (ceiling : record.toNat+88≤2713717616) :
    ∃ next : NodeRegistry (branchCounterEntry source record node child index occupied) frontier heap db,next.graph.valid=registry.graph.valid := by
  let target:=branchCounterEntry source record node child index occupied
  have domain : target.memaddrs=source.memaddrs := by unfold target branchCounterEntry occupancyState; split <;> rfl
  obtain ⟨graph,validEq,regions,disjoint,⟨values⟩⟩:=registry.graph.after_agreement source target 1024 frontier heap.toNat (WitnessValue db)
    registry.values registry.regions registry.disjoint domain (by
      intro query required
      have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions query required
      have outside:=registry.graph.excluded_footprint frontier heap.toNat registry.regions node 176 excluded query required
      exact branch_counter_outside_memory source record node child index occupied arena ceiling query (frontierLower.trans bounds.1) outside) (by
      intro query required
      have bounds:=registry.graph.value_bounds frontier heap.toNat registry.regions query required
      have outside:=registry.graph.excluded_value frontier heap.toNat registry.regions node 176 excluded query required
      exact branch_counter_outside_memory source record node child index occupied arena ceiling query (frontierLower.trans bounds.1) outside)
  exact ⟨⟨graph,values,regions,disjoint⟩,validEq⟩

/-- No child store reaches the branch's final value words, and the OCC
store remains below the branch. Thus their actual empty value persists. -/
theorem EmptyValue.counter_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17) (empty : EmptyValue source node)
    (arena : AllocatedBytes.Arena node 176) (floor : 2713731432≤node.toNat) (ceiling : record.toNat+88≤2713717616) :
    EmptyValue (branchCounterEntry source record node child index occupied) node := by
  have childNumber : (WitnessRecord.childAddress node index).toNat=node.toNat+(32+8*index.val) :=
    byteAddress_toNat node _ (by have upper:=arena.upper; have bound:=index.isLt; omega)
  have recordNumber : (record+40#64).toNat=record.toNat+40 := byteAddress_toNat record 40 (by omega)
  have agree (offset : Nat) (inside : 160≤offset ∧ offset<176) :
      (branchCounterEntry source record node child index occupied).memory (byteAddress node offset)=source.memory (byteAddress node offset) := by
    have number : (byteAddress node offset).toNat=node.toNat+offset := byteAddress_toNat node _ (by have upper:=arena.upper; omega)
    apply branch_counter_entry_memory source record node child index occupied _
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number,childNumber] at numeric
      have bound:=index.isLt
      omega
    · intro equal
      have numeric:=congrArg BitVec.toNat equal
      rw [number,recordNumber] at numeric
      omega
  exact empty.frame source _ node (agree 160 (by decide)) (agree 168 (by decide))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_counter_outside_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_counter
#print axioms InitECandidate.Solver.Mpt.WitnessCore.EmptyValue.counter_entry
