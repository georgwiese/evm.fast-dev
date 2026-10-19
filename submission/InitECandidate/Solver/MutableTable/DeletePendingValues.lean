import InitECandidate.Solver.MutableTable.DeleteInitial
import InitECandidate.Solver.MutableTable.DeleteMoveReads
import InitECandidate.Solver.MutableTable.OccupiedValueProperty

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- Values at the real active ordinals during backshift. The removed ordinal
and moving hole impose no requirement on stale or uninitialized words. -/
def PendingValues (source : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : Plan)
    {count : Nat} (deleted : Fin count) (entries : Fin count → Nat) (property : BitVec 64 → Prop) : Prop :=
  ∀ index,index≠deleted → ∀ value : BitVec 64,source.memory (cell plan .values (8*entries index))=.word value → property value

theorem PendingValues.of_memory (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (plan : Plan)
    {count : Nat} (deleted : Fin count) (entries : Fin count → Nat) (property : BitVec 64 → Prop)
    (values : PendingValues source plan deleted entries property) (same : target.memory=source.memory) :
    PendingValues target plan deleted entries property := by
  intro index active value stored
  rw [same] at stored
  exact values index active value stored

theorem PendingValues.initial (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (slots : List Nat)
    (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length)
    (property : BitVec 64 → Prop)
    (values : Get.OccupiedValuesHave source (cell plan .values 0) (BitVec.ofNat 64 plan.capacity) slots property) :
    PendingValues source plan deleted (Function.update (fun index : Fin slots.length=>slots.get index) deleted plan.capacity) property := by
  intro index active value stored
  rw [Function.update_of_ne active] at stored
  have inside := occupied.inside (slots.get index) (List.get_mem slots index)
  have small : slots.get index<2^64 := Nat.lt_trans inside (capacity_small kind plan valid)
  apply values (BitVec.ofNat 64 (slots.get index))
  · rw [BitVec.toNat_ofNat,BitVec.toNat_ofNat,Nat.mod_eq_of_lt small,Nat.mod_eq_of_lt (capacity_small kind plan valid)]
    exact inside
  · rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt small]
    exact List.get_mem slots index
  · rw [Move.natural_word_address kind plan valid .values (slots.get index) inside]
    exact stored

/-- The original movement changes one value cell to the actual moved value;
its key copy and order/position writes leave all other value cells alone. -/
theorem Move.value_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole<plan.capacity) (ordinalInside : ordinal<plan.capacity)
    (query : Nat) (inside : query<plan.capacity) :
    Move.memory source.memory source.be kind plan hole slot ordinal value (cell plan .values (8*query))=
      if query=hole then .word value else source.memory (cell plan .values (8*query)) := by
  have vectorInside : (BitVec.ofNat 64 hole).toNat<plan.capacity := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (Nat.lt_trans holeInside (capacity_small kind plan valid))]
    exact holeInside
  have extent : 8*query<size kind plan .values := by change 8*query<8*plan.capacity; omega
  rw [Move.memory,Move.metadata_pool_away _ kind plan valid hole ordinal holeInside ordinalInside .values (by decide) (by decide) _ extent]
  change StoreWord.put _ (cell plan .values 0+BitVec.ofNat 64 hole*8#64) value _=_
  rw [Move.natural_word_address kind plan valid .values hole holeInside]
  simp only [StoreWord.put,Move.word_cell_eq kind plan valid .values (Or.inl rfl) query hole inside holeInside]
  split
  · rfl
  · exact CopyGeneral.resultMemory_away source.memory source.be _ _ _ _
      (pool_key_away kind plan valid _ (BitVec.ofNat 64 hole) vectorInside .values (by decide) _ extent)

theorem PendingValues.after_move (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (pending : Pending source kind plan count deleted entries hole) (moved : Fin count) (active : moved≠deleted)
    (property : BitVec 64 → Prop) (values : PendingValues source plan deleted entries property)
    (value : BitVec 64) (valueCell : source.memory (cell plan .values (8*entries moved))=.word value) :
    PendingValues {source with memory:=Move.memory source.memory source.be kind plan hole (entries moved) moved.val value}
      plan deleted (Function.update entries moved hole) property := by
  intro index notDeleted found stored
  by_cases same : index=moved
  · subst index
    rw [Function.update_self] at stored
    change Move.memory source.memory source.be kind plan hole (entries moved) moved.val value (cell plan .values (8*hole))=.word found at stored
    rw [Move.value_cell source kind plan valid hole (entries moved) moved.val value pending.holeInside (Nat.lt_trans moved.isLt pending.room) hole pending.holeInside,if_pos rfl] at stored
    have equal : value=found := HolWordLab.word.inj stored
    rw [←equal]
    exact values moved active value valueCell
  · rw [Function.update_of_ne same] at stored
    change Move.memory source.memory source.be kind plan hole (entries moved) moved.val value (cell plan .values (8*entries index))=.word found at stored
    rw [Move.value_cell source kind plan valid hole (entries moved) moved.val value pending.holeInside (Nat.lt_trans moved.isLt pending.room) (entries index) (pending.inside index notDeleted),if_neg (pending.fresh index)] at stored
    exact values index notDeleted found stored

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.PendingValues.of_memory
#print axioms InitECandidate.Solver.MutableTable.Delete.PendingValues.initial
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.value_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.PendingValues.after_move
