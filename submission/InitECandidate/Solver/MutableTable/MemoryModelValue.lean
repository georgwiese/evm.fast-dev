import InitECandidate.Solver.MutableTable.MemoryModel
import InitECandidate.Solver.MutableTable.NaturalLayoutFrame
import InitECandidate.Solver.MutableTable.FindCellFrame

namespace InitECandidate.Solver.MutableTable.MemoryModel
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def valueMemory (memory : WordWrites.Memory) (plan : Plan) (index value : BitVec 64) : WordWrites.Memory :=
  StoreWord.put memory (cell plan .values 0 + index * 8#64) value

/-- Exact untouched-pool frame of the original setter's value store. -/
theorem value_pool_away (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (index value : BitVec 64) (inside : index.toNat < plan.capacity) (pool : Pool) (different : pool ≠ .values)
    (offset : Nat) (poolInside : offset < size kind plan pool) :
    valueMemory memory plan index value (cell plan pool offset) = memory (cell plan pool offset) := by
  rw [valueMemory, scaled_cell]
  exact if_neg (separate kind plan valid pool .values different offset _ poolInside
    (word_offset_inside kind plan .values index.toNat (Or.inl rfl) inside))

theorem header_offset_bound (kind : KeyHash.Kind) (plan : Plan) (count : BitVec 64) (offset : Nat) (value : BitVec 64)
    (member : (offset, value) ∈ headerEntries kind plan count) : offset < 72 := by
  simp only [headerEntries, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at member
  rcases member with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide

/-- All nine header meanings survive the actual existing-value update. -/
theorem Header.after_update (memory : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (index value count : BitVec 64) (inside : index.toNat < plan.capacity) (header : Header memory kind plan count) :
    Header (valueMemory memory plan index value) kind plan count := by
  intro offset stored member
  exact (value_pool_away memory kind plan valid index value inside .header (by decide) offset
    (header_offset_bound kind plan count offset stored member)).trans (header offset stored member)

/-- The original existing-value update preserves binary occupancy and the
actual dense order/position arrays, for arbitrary stored keys and values. -/
theorem Occupied.after_update (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (valid : Valid kind plan) (slots : List Nat) (room : slots.length ≤ plan.capacity) (occupied : Occupied source kind plan slots)
    (index value : BitVec 64) (inside : index.toNat < plan.capacity) :
    Occupied {source with memory := valueMemory source.memory plan index value} kind plan slots := by
  let post := {source with memory := valueMemory source.memory plan index value}
  refine ⟨occupied.distinct, occupied.inside, ?_, ?_, ?_⟩
  · intro slot slotInside
    have usedInside := used_offset_inside kind plan slot slotInside
    have queryCell : panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 slot) = cell plan .used (8 * (slot / 8)) := by
      change panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 slot) = _
      rw [constant_cell, byte_cell kind plan valid .used slot usedInside]
    have same : source.memory (panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 slot)) =
        post.memory (panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 slot)) := by
      rw [queryCell]
      exact (value_pool_away source.memory kind plan valid index value inside .used (by decide) _ (by omega)).symm
    rw [← Find.usedByte_of_cell source post (parameters kind plan 0#64) (BitVec.ofNat 64 slot) rfl rfl same]
    exact occupied.used slot slotInside
  · intro query
    have bounded : 8 * query.val < size kind plan .order := by
      have high := query.isLt
      change 8 * query.val < 8 * plan.capacity
      omega
    change valueMemory source.memory plan index value (cell plan .order (8 * query.val)) = _
    rw [value_pool_away source.memory kind plan valid index value inside .order (by decide) _ bounded]
    exact occupied.order query
  · intro query
    have slotInside := occupied.inside (slots.get query) (List.get_mem slots query)
    have bounded : 8 * slots.get query < size kind plan .position := by
      change 8 * slots.get query < 8 * plan.capacity
      omega
    change valueMemory source.memory plan index value (cell plan .position (8 * slots.get query)) = _
    rw [value_pool_away source.memory kind plan valid index value inside .position (by decide) _ bounded]
    exact occupied.position query

end InitECandidate.Solver.MutableTable.MemoryModel

#print axioms InitECandidate.Solver.MutableTable.MemoryModel.value_pool_away
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.header_offset_bound
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Header.after_update
#print axioms InitECandidate.Solver.MutableTable.MemoryModel.Occupied.after_update
