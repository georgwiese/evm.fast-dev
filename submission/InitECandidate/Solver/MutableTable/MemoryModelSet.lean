import InitECandidate.Solver.MutableTable.MemoryModelInsert
import InitECandidate.Solver.MutableTable.MemoryModelValue
import InitECandidate.Solver.MutableTable.MemoryModelFields
import InitECandidate.Solver.MutableTable.SetEffect

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The exact physical effect exported by the unchanged setter preserves the
runtime representation. The dense list either stays fixed or appends the
previously empty slot; key comparisons and collisions need no assumptions. -/
theorem setter_effect (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (room : slots.length < plan.capacity)
    (header : Header source.memory kind plan (BitVec.ofNat 64 slots.length))
    (occupied : Occupied source kind plan slots) (query value : BitVec 64) (memory : WordWrites.Memory)
    (effect : Set.Effect source kind (parameters kind plan query) (cell plan .header 0)
      (cell plan .values 0) (cell plan .order 0) (cell plan .position 0) (BitVec.ofNat 64 slots.length) value memory) :
    ∃ next : List Nat, (next = slots ∨ ∃ slot, next = slots ++ [slot]) ∧
      Header memory kind plan (BitVec.ofNat 64 next.length) ∧
      Occupied {source with memory := memory} kind plan next := by
  have capNat : (parameters kind plan query).capacity.toNat = plan.capacity := by
    change (BitVec.ofNat 64 plan.capacity).toNat = plan.capacity
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (capacity_small kind plan valid)]
  rcases effect with ⟨index, inside, used, stored⟩ | ⟨index, inside, used, stored⟩
  · rw [capNat] at inside
    subst memory
    exact ⟨slots, Or.inl rfl, Header.after_update source.memory kind plan valid index value _ inside header,
      Occupied.after_update source kind plan valid slots (Nat.le_of_lt room) occupied index value inside⟩
  · rw [capNat] at inside
    have countInside : (BitVec.ofNat 64 slots.length).toNat < plan.capacity := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind plan valid))]
      exact room
    have increment : BitVec.ofNat 64 (slots ++ [index.toNat]).length = BitVec.ofNat 64 slots.length + 1#64 := by
      simp only [List.length_append, List.length_singleton, BitVec.ofNat_add]
    subst memory
    refine ⟨slots ++ [index.toNat], Or.inr ⟨index.toNat, rfl⟩, ?_, ?_⟩
    · rw [increment]
      exact Header.after_insert source.memory source.be kind plan valid query index _ value inside countInside header
    · exact Occupied.after_insert source kind plan valid domain little slots room occupied query index value inside used

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.setter_effect
