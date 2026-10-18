import InitECandidate.Solver.MutableTable.DeleteSlots
import InitECandidate.Solver.MutableTable.MemoryModelFields

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Physical invariant while the original deletion shifts a hole. The
removed ordinal has an out-of-range proof sentinel; its real word is ignored
until the final last-entry swap. This is proof state, not a program change. -/
structure Pending (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat) : Prop where
  room : count < plan.capacity
  distinct : Function.Injective entries
  sentinel : entries deleted = plan.capacity
  inside : ∀ index, index ≠ deleted → entries index < plan.capacity
  holeInside : hole < plan.capacity
  fresh : ∀ index, entries index ≠ hole
  binary : ∀ slot < plan.capacity, Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some 0 ∨
    Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some 1
  used : ∀ slot < plan.capacity, Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some 1 ↔ Covered entries deleted hole slot
  order : ∀ index, index ≠ deleted → source.memory (cell plan .order (8 * index.val)) = .word (BitVec.ofNat 64 (entries index))
  position : ∀ index, index ≠ deleted → source.memory (cell plan .position (8 * entries index)) = .word (BitVec.ofNat 64 index.val)

theorem Pending.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole)
    (memory : source.memory = target.memory) (domain : source.memaddrs = target.memaddrs) (endian : source.be = target.be) :
    Pending target kind plan count deleted entries hole := by
  refine ⟨pending.room, pending.distinct, pending.sentinel, pending.inside, pending.holeInside, pending.fresh, ?_, ?_, ?_, ?_⟩
  · intro slot inside
    rw [← Find.usedByte_of_fields source target _ _ memory domain endian]
    exact pending.binary slot inside
  · intro slot inside
    rw [← Find.usedByte_of_fields source target _ _ memory domain endian]
    exact pending.used slot inside
  · intro index active
    rw [← memory]
    exact pending.order index active
  · intro index active
    rw [← memory]
    exact pending.position index active

/-- A scanned used slot distinct from the moving hole has a real active
ordinal, hence a readable inverse-position word strictly below the count. -/
theorem Pending.active (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole slot : Nat)
    (pending : Pending source kind plan count deleted entries hole) (inside : slot < plan.capacity)
    (used : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = some 1) (different : slot ≠ hole) :
    ∃ index, index ≠ deleted ∧ entries index = slot ∧ source.memory (cell plan .position (8 * slot)) = .word (BitVec.ofNat 64 index.val) := by
  rcases (pending.used slot inside).mp used with same | ⟨index, active, actual⟩
  · exact (different same).elim
  · refine ⟨index, active, actual, ?_⟩
    rw [← actual]
    exact pending.position index active

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.Pending.of_fields
#print axioms InitECandidate.Solver.MutableTable.Delete.Pending.active
