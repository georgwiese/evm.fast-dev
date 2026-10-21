import InitECandidate.Solver.Mpt.WitnessCoreRegistryBranchPrefix

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The actual continuing-branch index store lies wholly in scratch. -/
theorem advanced_above_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (index : Fin 16)
    (ceiling : record.toNat+88≤2713717616) (query : BitVec 64) (above : 2713717616≤query.toNat) :
    (advanced source record index).memory query=source.memory query := by
  have number : (record+32#64).toNat=record.toNat+32 := byteAddress_toNat record 32 (by omega)
  have away : query≠record+32#64 := by intro equal; have numeric:=congrArg BitVec.toNat equal; rw [number] at numeric; omega
  exact if_neg away

theorem advanced_database_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap record : BitVec 64) (index : Fin 16)
    (ceiling : record.toNat+88≤2713717616) : DatabaseFrame source (advanced source record index) heap :=
  ⟨rfl,rfl,rfl,fun query above _=>advanced_above_memory source record index ceiling query above⟩

theorem Children.advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory) (valid : BitVec 64 → Prop)
    (record node : BitVec 64) (index : Fin 16) (count : Nat) (children : Children source valid node count) (bounded : count≤16)
    (arena : AllocatedBytes.Arena node 176) (floor : 2713731432≤node.toNat) (ceiling : record.toNat+88≤2713717616) :
    Children (advanced source record index) valid node count := by
  apply children.frame source _ valid node count
  intro current inside
  have number : (byteAddress node (32+8*current)).toNat=node.toNat+(32+8*current) := byteAddress_toNat node _ (by have upper:=arena.upper; omega)
  exact advanced_above_memory source record index ceiling _ (by omega)

theorem EmptyValue.advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node : BitVec 64) (index : Fin 16)
    (empty : EmptyValue source node) (arena : AllocatedBytes.Arena node 176)
    (floor : 2713731432≤node.toNat) (ceiling : record.toNat+88≤2713717616) : EmptyValue (advanced source record index) node := by
  have number160 : (node+160#64).toNat=node.toNat+160 := byteAddress_toNat node 160 (by have upper:=arena.upper; omega)
  have number168 : (node+168#64).toNat=node.toNat+168 := byteAddress_toNat node 168 (by have upper:=arena.upper; omega)
  exact empty.frame source _ node (advanced_above_memory source record index ceiling _ (by omega))
    (advanced_above_memory source record index ceiling _ (by omega))

theorem NodeRegistry.branch_counter_tags (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17)
    (registry : NodeRegistry source frontier heap db) (frontierLower : 2713731432≤frontier)
    (excluded : registry.graph.Excludes node 176) (arena : AllocatedBytes.Arena node 176) (ceiling : record.toNat+88≤2713717616) :
    ∀ pointer,registry.graph.valid pointer → pointer≠0#64 →
      wordAt (branchCounterEntry source record node child index occupied).memory pointer=wordAt source.memory pointer := by
  intro pointer member active
  have required : registry.graph.Footprint pointer := .header pointer member active
  have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions pointer required
  have outside:=registry.graph.excluded_footprint frontier heap.toNat registry.regions node 176 excluded pointer required
  unfold wordAt
  rw [branch_counter_outside_memory source record node child index occupied arena ceiling pointer (frontierLower.trans bounds.1) outside]

/-- The whole real continuing-child state retains exactly the old
completed registry while the pending node gains its next initialized slot. -/
theorem NodeRegistry.branch_advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap record node child : BitVec 64) (index nextIndex : Fin 16) (occupied : Fin 17)
    (registry : NodeRegistry source frontier heap db) (frontierLower : 2713731432≤frontier)
    (excluded : registry.graph.Excludes node 176) (arena : AllocatedBytes.Arena node 176) (ceiling : record.toNat+88≤2713717616) :
    ∃ next : NodeRegistry (advanced (branchCounterEntry source record node child index occupied) record nextIndex) frontier heap db,
      next.graph.valid=registry.graph.valid := by
  let middle:=branchCounterEntry source record node child index occupied
  obtain ⟨current,currentValid⟩:=registry.branch_counter source frontier db heap record node child index occupied frontierLower excluded arena ceiling
  have frame:=advanced_database_frame middle heap record nextIndex ceiling
  obtain ⟨next,nextValid⟩:=current.after_database_frame middle _ frontier heap db (by omega) frame
  exact ⟨next,nextValid.trans currentValid⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.advanced_database_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.Children.advanced
#print axioms InitECandidate.Solver.Mpt.WitnessCore.EmptyValue.advanced
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_counter_tags
#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_advanced
