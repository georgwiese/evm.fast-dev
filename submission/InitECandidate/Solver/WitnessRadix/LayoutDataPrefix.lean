import InitECandidate.Solver.WitnessRadix.LayoutContext

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

theorem data_not_allocation (layout : Layout) (allocated depth index : Nat) (destination : Address) (pool : Pool)
    (buffer : pool = .primary ∨ pool = .backup) (indexBound : index < layout.count)
    (incoming : IncomingOffset layout allocated destination.1 destination.2) :
    (pool, 8 * index) ∉ allocationAddresses layout allocated depth destination := by
  have different : (pool, 8 * index) ≠ destination := by
    intro same
    subst destination
    rcases buffer with rfl | rfl <;> exact False.elim incoming
  rcases buffer with rfl | rfl <;>
    simp [allocationAddresses, different, Ne.symm different] <;> omega

theorem data_allocation_separate (layout : Layout) (valid : Valid layout) (allocated depth index : Nat)
    (destination : Address) (pool : Pool) (buffer : pool = .primary ∨ pool = .backup)
    (indexBound : index < layout.count) (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (incoming : IncomingOffset layout allocated destination.1 destination.2) :
    cell layout pool (8 * index) ∉ (allocationAddresses layout allocated depth destination).map (address layout) := by
  have room := valid.room
  intro member
  obtain ⟨entry, entryMember, same⟩ := List.mem_map.mp member
  have entryBound := write_offset_bound layout valid _ _
    (allocation_address_write layout valid allocated depth destination branchRoom stackRoom incoming entry entryMember)
  have dataBound : 8 * index < size layout pool := by
    rcases buffer with rfl | rfl <;> change _ < 8 * layout.capacity <;> omega
  have equal := address_injective layout valid entry (pool, 8 * index) entryBound dataBound same
  exact data_not_allocation layout allocated depth index destination pool buffer indexBound incoming (equal ▸ entryMember)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.data_not_allocation
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.data_allocation_separate
