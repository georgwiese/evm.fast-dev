import InitECandidate.Solver.MutableTable.DeletePending
import InitECandidate.Solver.MutableTable.MemoryModelInsertFields

namespace InitECandidate.Solver.MutableTable.Delete.Move
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def copiedMemory (memory : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (hole slot : Nat) (value : BitVec 64) : WordWrites.Memory :=
  MemoryModel.copiedValueMemory memory be kind plan (cell plan .keys 0 + BitVec.ofNat 64 slot * BitVec.ofNat 64 (stride kind)) (BitVec.ofNat 64 hole) value

def writes (plan : Plan) (hole ordinal : Nat) : List (BitVec 64 × BitVec 64) :=
  [(cell plan .order (8 * ordinal), BitVec.ofNat 64 hole), (cell plan .position (8 * hole), BitVec.ofNat 64 ordinal)]

/-- Exact copy/value/order/position memory of the original movable branch.
There is no used-byte store or item-count change in this branch. -/
def memory (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (hole slot ordinal : Nat) (value : BitVec 64) : WordWrites.Memory :=
  WordWrites.write (copiedMemory input be kind plan hole slot value) (writes plan hole ordinal)

theorem copied_pool_away (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (pool : Pool) (notKeys : pool ≠ .keys) (notValues : pool ≠ .values)
    (offset : Nat) (inside : offset < size kind plan pool) : copiedMemory input be kind plan hole slot value (cell plan pool offset) = input (cell plan pool offset) := by
  have vectorInside : (BitVec.ofNat 64 hole).toNat < plan.capacity := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans holeInside (capacity_small kind plan valid))]
    exact holeInside
  exact MemoryModel.copied_value_pool_away input be kind plan valid _ _ value vectorInside pool notKeys notValues offset inside

theorem metadata_pool_away (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole ordinal : Nat) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (pool : Pool) (notOrder : pool ≠ .order) (notPosition : pool ≠ .position) (offset : Nat) (inside : offset < size kind plan pool) :
    WordWrites.write input (writes plan hole ordinal) (cell plan pool offset) = input (cell plan pool offset) := by
  apply WordWrites.write_away
  simp only [writes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, not_or, not_false_eq_true, and_true]
  exact ⟨separate kind plan valid pool .order notOrder offset _ inside (by change 8 * ordinal < 8 * plan.capacity; omega),
    separate kind plan valid pool .position notPosition offset _ inside (by change 8 * hole < 8 * plan.capacity; omega)⟩

theorem pool_away (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (pool : Pool) (notKeys : pool ≠ .keys) (notValues : pool ≠ .values) (notOrder : pool ≠ .order) (notPosition : pool ≠ .position)
    (offset : Nat) (inside : offset < size kind plan pool) : memory input be kind plan hole slot ordinal value (cell plan pool offset) = input (cell plan pool offset) := by
  rw [memory, metadata_pool_away _ kind plan valid hole ordinal holeInside ordinalInside pool notOrder notPosition offset inside]
  exact copied_pool_away input be kind plan valid hole slot value holeInside pool notKeys notValues offset inside

theorem word_cell_eq (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (pool : Pool)
    (wordPool : pool = .values ∨ pool = .order ∨ pool = .position) (first second : Nat) (firstInside : first < plan.capacity) (secondInside : second < plan.capacity) :
    (cell plan pool (8 * first) = cell plan pool (8 * second)) ↔ first = second := by
  constructor
  · intro same
    by_contra different
    exact cell_injective kind plan valid pool _ _ (by have := word_offset_inside kind plan pool first wordPool firstInside; omega)
      (by have := word_offset_inside kind plan pool second wordPool secondInside; omega) (by omega) same
  · rintro rfl
    rfl

theorem order_cell (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (query : Nat) (inside : query < plan.capacity) :
    memory input be kind plan hole slot ordinal value (cell plan .order (8 * query)) =
      if query = ordinal then .word (BitVec.ofNat 64 hole) else input (cell plan .order (8 * query)) := by
  have away := separate kind plan valid .order .position (by decide) (8 * query) (8 * hole)
    (by change 8 * query < 8 * plan.capacity; omega) (by change 8 * hole < 8 * plan.capacity; omega)
  simp only [memory, writes, WordWrites.write, StoreWord.put, if_neg away]
  simp only [word_cell_eq kind plan valid .order (Or.inr (Or.inl rfl)) query ordinal inside ordinalInside,
    copied_pool_away input be kind plan valid hole slot value holeInside .order (by decide) (by decide) _ (by change 8 * query < 8 * plan.capacity; omega)]

theorem position_cell (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (query : Nat) (inside : query < plan.capacity) :
    memory input be kind plan hole slot ordinal value (cell plan .position (8 * query)) =
      if query = hole then .word (BitVec.ofNat 64 ordinal) else input (cell plan .position (8 * query)) := by
  have away := separate kind plan valid .position .order (by decide) (8 * query) (8 * ordinal)
    (by change 8 * query < 8 * plan.capacity; omega) (by change 8 * ordinal < 8 * plan.capacity; omega)
  simp only [memory, writes, WordWrites.write, StoreWord.put, if_neg away]
  simp only [word_cell_eq kind plan valid .position (Or.inr (Or.inr rfl)) query hole inside holeInside,
    copied_pool_away input be kind plan valid hole slot value holeInside .position (by decide) (by decide) _ (by change 8 * query < 8 * plan.capacity; omega)]

theorem used_byte (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (query : Nat) (inside : query < plan.capacity) :
    Find.usedByte {source with memory := memory source.memory source.be kind plan hole slot ordinal value} (parameters kind plan 0#64) (BitVec.ofNat 64 query) =
      Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 query) := by
  let post := {source with memory := memory source.memory source.be kind plan hole slot ordinal value}
  have extent := used_offset_inside kind plan query inside
  have queryCell : panByteAlignHOL (width := 64) ((parameters kind plan 0#64).used + BitVec.ofNat 64 query) = cell plan .used (8 * (query / 8)) := by
    change panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 query) = _
    rw [constant_cell, byte_cell kind plan valid .used query extent]
  apply Find.usedByte_of_cell post source _ _ rfl rfl
  rw [queryCell]
  exact pool_away source.memory source.be kind plan valid hole slot ordinal value holeInside ordinalInside .used (by decide) (by decide) (by decide) (by decide) _ (by omega)

theorem header (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value count : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity)
    (original : MemoryModel.Header input kind plan count) : MemoryModel.Header (memory input be kind plan hole slot ordinal value) kind plan count := by
  intro offset stored member
  exact (pool_away input be kind plan valid hole slot ordinal value holeInside ordinalInside .header (by decide) (by decide) (by decide) (by decide) offset
    (MemoryModel.header_offset_bound kind plan count offset stored member)).trans (original offset stored member)

end InitECandidate.Solver.MutableTable.Delete.Move

#print axioms InitECandidate.Solver.MutableTable.Delete.Move.copied_pool_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.metadata_pool_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.pool_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.word_cell_eq
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.order_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.position_cell
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.used_byte
#print axioms InitECandidate.Solver.MutableTable.Delete.Move.header
