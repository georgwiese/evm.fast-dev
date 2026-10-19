import InitECandidate.Solver.MutableTable.MemoryModelSetValues
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
  obtain ⟨next, shape, nextHeader, nextOccupied, _⟩ := setter_effect_values source kind plan valid domain little
    slots room header occupied query value memory (fun _=>True) (fun _ _ _ _ _=>True.intro) True.intro effect
  exact ⟨next, shape, nextHeader, nextOccupied⟩

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.setter_effect
