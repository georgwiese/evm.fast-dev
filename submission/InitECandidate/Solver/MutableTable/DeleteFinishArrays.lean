import InitECandidate.Solver.MutableTable.DeleteFinishFields

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

theorem order_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (query : Nat) (inside : query < plan.capacity) :
    memory source.memory plan deleted entries hole (cell plan .order (8 * query)) =
      if deleted.val = count - 1 then source.memory (cell plan .order (8 * query))
      else if query = deleted.val then .word (BitVec.ofNat 64 (entries (lastOrdinal deleted)))
      else source.memory (cell plan .order (8 * query)) := by
  have extent : 8 * query < size kind plan .order := by change 8 * query < 8 * plan.capacity; omega
  have headerAway := separate kind plan valid .order .header (by decide) (8 * query) 24 extent (by change 24 < 72; decide)
  have cleared := cleared_pool_away source.memory kind plan valid hole pending.holeInside .order (by decide) (8 * query) extent
  by_cases last : deleted.val = count - 1
  · simp only [memory, writes, if_pos last, WordWrites.write, StoreWord.put, if_neg headerAway, cleared]
  · have slotInside := pending.inside (lastOrdinal deleted) (last_active deleted last)
    have positionAway := separate kind plan valid .order .position (by decide) (8 * query) (8 * entries (lastOrdinal deleted)) extent (by change 8 * entries (lastOrdinal deleted) < 8 * plan.capacity; omega)
    simp only [memory, writes, if_neg last, WordWrites.write, StoreWord.put, if_neg headerAway, if_neg positionAway,
      Move.word_cell_eq kind plan valid .order (Or.inr (Or.inl rfl)) query deleted.val inside (Nat.lt_trans deleted.isLt pending.room), cleared]

theorem position_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (query : Nat) (inside : query < plan.capacity) :
    memory source.memory plan deleted entries hole (cell plan .position (8 * query)) =
      if deleted.val = count - 1 then source.memory (cell plan .position (8 * query))
      else if query = entries (lastOrdinal deleted) then .word (BitVec.ofNat 64 deleted.val)
      else source.memory (cell plan .position (8 * query)) := by
  have extent : 8 * query < size kind plan .position := by change 8 * query < 8 * plan.capacity; omega
  have headerAway := separate kind plan valid .position .header (by decide) (8 * query) 24 extent (by change 24 < 72; decide)
  have cleared := cleared_pool_away source.memory kind plan valid hole pending.holeInside .position (by decide) (8 * query) extent
  by_cases last : deleted.val = count - 1
  · simp only [memory, writes, if_pos last, WordWrites.write, StoreWord.put, if_neg headerAway, cleared]
  · have slotInside := pending.inside (lastOrdinal deleted) (last_active deleted last)
    have orderAway := separate kind plan valid .position .order (by decide) (8 * query) (8 * deleted.val) extent (by change 8 * deleted.val < 8 * plan.capacity; have := deleted.isLt; have := pending.room; omega)
    simp only [memory, writes, if_neg last, WordWrites.write, StoreWord.put, if_neg headerAway, if_neg orderAway,
      Move.word_cell_eq kind plan valid .position (Or.inr (Or.inr rfl)) query (entries (lastOrdinal deleted)) inside slotInside, cleared]

theorem final_order (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (index : Fin (count - 1)) :
    memory source.memory plan deleted entries hole (cell plan .order (8 * index.val)) = .word (BitVec.ofNat 64 (entries (remainingOrdinal deleted index))) := by
  have indexBound := index.isLt
  have indexInside : index.val < plan.capacity := by have := pending.room; omega
  rw [order_cell source kind plan valid count deleted entries hole pending index.val indexInside]
  by_cases same : index.val = deleted.val
  · have notLast : deleted.val ≠ count - 1 := by omega
    simp only [if_neg notLast, if_pos same, remainingOrdinal, lastOrdinal]
  · let original : Fin count := ⟨index.val, by omega⟩
    have active : original ≠ deleted := fun equal => same (congrArg Fin.val equal)
    have old := pending.order original active
    by_cases last : deleted.val = count - 1
    · simpa only [if_pos last, remainingOrdinal, if_neg same] using old
    · simpa only [if_neg last, if_neg same, remainingOrdinal] using old

theorem final_position (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (index : Fin (count - 1)) :
    memory source.memory plan deleted entries hole (cell plan .position (8 * entries (remainingOrdinal deleted index))) = .word (BitVec.ofNat 64 index.val) := by
  have indexBound := index.isLt
  rw [position_cell source kind plan valid count deleted entries hole pending _ (pending.inside _ (remaining_active deleted index))]
  by_cases same : index.val = deleted.val
  · have notLast : deleted.val ≠ count - 1 := by omega
    simp only [if_neg notLast, remainingOrdinal, if_pos same, lastOrdinal, ↓reduceIte, same]
  · let original : Fin count := ⟨index.val, by omega⟩
    have active : original ≠ deleted := fun equal => same (congrArg Fin.val equal)
    have different : entries original ≠ entries (lastOrdinal deleted) := by
      intro equal
      have numeric := congrArg Fin.val (pending.distinct equal)
      change index.val = count - 1 at numeric
      omega
    have old := pending.position original active
    by_cases last : deleted.val = count - 1
    · simpa only [if_pos last, remainingOrdinal, if_neg same] using old
    · have remainingEq : remainingOrdinal deleted index = original := by
        simp only [remainingOrdinal, if_neg same]
        rfl
      rw [if_neg last, remainingEq, if_neg different]
      exact old

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.order_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.position_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.final_order
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.final_position
