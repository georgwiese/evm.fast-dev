import InitECandidate.Solver.MutableTable.GrowRuntime.Locals

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def setupPrice (capacity : Nat) : Nat := Zero.price capacity + 6

theorem prepared_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count : Nat) :
    (preparedState source kind old start count).clock = source.clock - setupPrice (2 * old.capacity) := by
  change source.clock - 1 - 1 - 1 - 1 - 1 - (Zero.price (2 * old.capacity) + 1) = source.clock - (Zero.price (2 * old.capacity) + 6)
  omega

theorem prepared_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan) (start count : Nat) :
    emptyLocalsHOLFinite (preparedState source kind old start count) = emptyLocalsHOLFinite {source with
      globals := source.globals.update (ofString "heap_ptr", .val (.word (BitVec.ofNat 64 (relocatedEnd kind start (2 * old.capacity)))))
      memory := (resetMemory source.memory (relocated kind (old.base .header) start (2 * old.capacity)))
      clock := source.clock - setupPrice (2 * old.capacity)} := by
  have clock := prepared_clock source kind old start count
  rw [show emptyLocalsHOLFinite (preparedState source kind old start count) = emptyLocalsHOLFinite
    {preparedState source kind old start count with clock := source.clock - setupPrice (2 * old.capacity)} by rw [← clock]]
  simp only [preparedState, allocatedState, orderState, usedState, valueState, keyState, headerState,
    PersistentAlloc.nextState, WitnessRadix.QueryBranch.bind, setVarHOLFinite, emptyLocalsHOLFinite, TableNew.update_twice]

/-- Actual reset memory preserves every old array cell needed by rehash.
The physical header is shared and is excluded from this frame. -/
theorem reset_old_array (memory : WordWrites.Memory) (kind : KeyHash.Kind) (old : Plan) (oldValid : Valid kind old)
    (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (pool : Pool) (array : pool ≠ .header) (offset : Nat) (inside : offset < size kind old pool) :
    resetMemory memory (relocated kind (old.base .header) start capacity) (cell old pool offset) = memory (cell old pool offset) := by
  let plan := relocated kind (old.base .header) start capacity
  have before : (cell old pool offset).toNat < start := by
    rw [number kind old oldValid pool offset inside]
    have high := earlier pool
    omega
  have storesAway : cell old pool offset ∉ (resetWrites plan).map Prod.fst := by
    rw [reset_cells]
    intro member
    obtain ⟨other, belongs, same⟩ := List.mem_map.mp member
    exact separate kind old oldValid .header pool (Ne.symm array) other offset (reset_site_bound other belongs) inside same
  rw [resetMemory, WordWrites.write_away _ _ _ storesAway]
  apply Zero.final_memory_away
  intro byte byteInside
  change cell old pool offset ≠ cell plan .used 0 + BitVec.ofNat 64 byte
  rw [constant_cell]
  exact relocated_array_away kind (old.base .header) start capacity newValid _ (Or.inl before) .used (by decide) byte (used_offset_inside kind plan byte byteInside)

theorem prepared_model (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (start count : Nat) (valid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (multiple : (2 * old.capacity) % 8 = 0) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false) :
    MemoryModel.Occupied (preparedState source kind old start count) kind (relocated kind (old.base .header) start (2 * old.capacity)) [] := by
  have model := reset_model source kind _ valid multiple domain little
  exact MemoryModel.Occupied.of_fields _ _ kind _ [] model rfl rfl rfl

theorem prepared_header (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (start count : Nat) (valid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 count)) :
    MemoryModel.Header (preparedState source kind old start count).memory kind (relocated kind (old.base .header) start (2 * old.capacity)) 0#64 := by
  apply reset_header source.memory kind _ valid
  · exact header 0 _ (by simp [MemoryModel.headerEntries])
  · exact header 8 _ (by simp [MemoryModel.headerEntries])

theorem prepared_old_arrays (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start count : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start) :
    OldArrays (preparedState source kind old start count) source kind old := by
  intro pool array offset inside
  exact reset_old_array source.memory kind old oldValid start _ newValid earlier pool array offset inside

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_clock
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_frame
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reset_old_array
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_model
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_header
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.prepared_old_arrays
