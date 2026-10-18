import InitECandidate.Solver.MutableTable.DeletePending
import InitECandidate.Solver.MutableTable.DeleteFinalSlots
import InitECandidate.Solver.MutableTable.DeleteMoveReads

namespace InitECandidate.Solver.MutableTable.Delete.Finish
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

def lastOrdinal {count : Nat} (deleted : Fin count) : Fin count := ⟨count - 1, by have := deleted.isLt; omega⟩

def writes {count : Nat} (plan : Plan) (deleted : Fin count) (entries : Fin count → Nat) : List (BitVec 64 × BitVec 64) :=
  if deleted.val = count - 1 then [(cell plan .header 24, BitVec.ofNat 64 (count - 1))]
  else [(cell plan .order (8 * deleted.val), BitVec.ofNat 64 (entries (lastOrdinal deleted))),
    (cell plan .position (8 * entries (lastOrdinal deleted)), BitVec.ofNat 64 deleted.val),
    (cell plan .header 24, BitVec.ofNat 64 (count - 1))]

def clearedMemory (input : WordWrites.Memory) (plan : Plan) (hole : Nat) : WordWrites.Memory :=
  ByteStore.write input (cell plan .used 0 + BitVec.ofNat 64 hole) 0

def memory {count : Nat} (input : WordWrites.Memory) (plan : Plan) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat) : WordWrites.Memory :=
  WordWrites.write (clearedMemory input plan hole) (writes plan deleted entries)

theorem last_active {count : Nat} (deleted : Fin count) (swap : deleted.val ≠ count - 1) : lastOrdinal deleted ≠ deleted := by
  intro same
  exact swap (congrArg Fin.val same).symm

theorem cleared_pool_away (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole : Nat) (holeInside : hole < plan.capacity) (pool : Pool) (notUsed : pool ≠ .used)
    (offset : Nat) (inside : offset < size kind plan pool) :
    clearedMemory input plan hole (cell plan pool offset) = input (cell plan pool offset) := by
  have extent := used_offset_inside kind plan hole holeInside
  have byteCell : panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 hole) = cell plan .used (8 * (hole / 8)) := by
    rw [constant_cell, byte_cell kind plan valid .used hole extent]
  have different := separate kind plan valid pool .used notUsed offset (8 * (hole / 8)) inside (by omega)
  simp [clearedMemory, ByteStore.write, StoreWord.put, byteCell, different]

theorem writes_pool_away (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (room : count < plan.capacity)
    (activeInside : ∀ index, index ≠ deleted → entries index < plan.capacity)
    (pool : Pool) (notOrder : pool ≠ .order) (notPosition : pool ≠ .position) (notHeader : pool ≠ .header)
    (offset : Nat) (inside : offset < size kind plan pool) :
    WordWrites.write input (writes plan deleted entries) (cell plan pool offset) = input (cell plan pool offset) := by
  apply WordWrites.write_away
  have ordinalInside : deleted.val < plan.capacity := Nat.lt_trans deleted.isLt room
  have headerAway := separate kind plan valid .header pool (Ne.symm notHeader) 24 offset (by change 24 < 72; decide) inside
  by_cases last : deleted.val = count - 1
  · simpa only [writes, if_pos last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using Ne.symm headerAway
  · have slotInside := activeInside (lastOrdinal deleted) (last_active deleted last)
    have orderAway := separate kind plan valid .order pool (Ne.symm notOrder) (8 * deleted.val) offset (by change 8 * deleted.val < 8 * plan.capacity; omega) inside
    have positionAway := separate kind plan valid .position pool (Ne.symm notPosition) (8 * entries (lastOrdinal deleted)) offset (by change 8 * entries (lastOrdinal deleted) < 8 * plan.capacity; omega) inside
    simp only [writes, if_neg last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨Ne.symm orderAway, Ne.symm positionAway, Ne.symm headerAway⟩

theorem writes_distinct (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (room : count < plan.capacity)
    (activeInside : ∀ index, index ≠ deleted → entries index < plan.capacity) :
    ((writes plan deleted entries).map Prod.fst).Nodup := by
  have ordinalInside : deleted.val < plan.capacity := Nat.lt_trans deleted.isLt room
  by_cases last : deleted.val = count - 1
  · simp [writes, last]
  · have slotInside := activeInside (lastOrdinal deleted) (last_active deleted last)
    have orderInside : 8 * deleted.val < size kind plan .order := by change 8 * deleted.val < 8 * plan.capacity; omega
    have positionInside : 8 * entries (lastOrdinal deleted) < size kind plan .position := by change 8 * entries (lastOrdinal deleted) < 8 * plan.capacity; omega
    have orderPosition := separate kind plan valid .order .position (by decide) _ _ orderInside positionInside
    have orderHeader := separate kind plan valid .order .header (by decide) _ 24 orderInside (by change 24 < 72; decide)
    have positionHeader := separate kind plan valid .position .header (by decide) _ 24 positionInside (by change 24 < 72; decide)
    simp [writes, last, orderPosition, orderHeader, positionHeader]

end InitECandidate.Solver.MutableTable.Delete.Finish

#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.last_active
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.cleared_pool_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.writes_pool_away
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.writes_distinct
