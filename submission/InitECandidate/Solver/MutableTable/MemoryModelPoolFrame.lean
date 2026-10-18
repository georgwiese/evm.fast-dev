import InitECandidate.Solver.MutableTable.MemoryModelBounds
import InitECandidate.Solver.MutableTable.MemoryModelFields

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Word preservation throughout all six physically owned pools. -/
def PoolFrame (input output : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) : Prop :=
  ∀ pool offset, offset < size kind plan pool → output (cell plan pool offset) = input (cell plan pool offset)

theorem PoolFrame.refl (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) : PoolFrame input input kind plan := by
  intro pool offset inside; rfl

theorem PoolFrame.trans (input middle output : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan)
    (first : PoolFrame input middle kind plan) (second : PoolFrame middle output kind plan) : PoolFrame input output kind plan := by
  intro pool offset inside
  exact (second pool offset inside).trans (first pool offset inside)

theorem Header.of_pool_frame (input output : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (count : BitVec 64)
    (header : Header input kind plan count) (frame : PoolFrame input output kind plan) : Header output kind plan count := by
  intro offset value member
  have inside : offset < 72 := by
    simp only [headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
    rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  exact (frame .header offset inside).trans (header offset value member)

/-- An outside writer preserves the complete physical table model. Its
used-byte reads require preserving the entire aligned backing word. -/
theorem Occupied.of_pool_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (slots : List Nat) (occupied : Occupied source kind plan slots)
    (domain : target.memaddrs = source.memaddrs) (endian : target.be = source.be) (frame : PoolFrame source.memory target.memory kind plan) :
    Occupied target kind plan slots := by
  have lengthBound := Occupied.length_le source kind plan slots occupied
  refine ⟨occupied.distinct, occupied.inside, ?_, ?_, ?_⟩
  · intro slot inside
    have queryCell : panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 slot) = cell plan .used (8 * (slot / 8)) := by
      change panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 slot) = _
      rw [constant_cell, byte_cell kind plan valid .used slot (used_offset_inside kind plan slot inside)]
    have kept : Find.usedByte target (parameters kind plan 0#64) (BitVec.ofNat 64 slot) = Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 slot) := by
      apply Find.usedByte_of_cell target source _ _ domain endian
      rw [queryCell]
      exact frame .used _ (by have := used_offset_inside kind plan slot inside; omega)
    exact kept.trans (occupied.used slot inside)
  · intro index
    exact (frame .order (8 * index.val) (by change 8 * index.val < 8 * plan.capacity; have := index.isLt; omega)).trans (occupied.order index)
  · intro index
    have inside := occupied.inside _ (List.get_mem slots index)
    exact (frame .position (8 * slots.get index) (by change 8 * slots.get index < 8 * plan.capacity; omega)).trans (occupied.position index)

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.PoolFrame.refl
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.PoolFrame.trans
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Header.of_pool_frame
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Occupied.of_pool_frame
