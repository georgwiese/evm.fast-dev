import InitECandidate.Solver.MutableTable.DeleteMoveMemory
import InitECandidate.Solver.MutableTable.DeleteFinishMemory
import InitECandidate.Solver.MutableTable.TableFootprint

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack WitnessRadix NaturalLayout

theorem Move.footprint (input : WordWrites.Memory) (be : Bool) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (hole slot ordinal : Nat) (value : BitVec 64) (holeInside : hole < plan.capacity) (ordinalInside : ordinal < plan.capacity) :
    TableFootprint.Frame input (Move.memory input be kind plan hole slot ordinal value) kind plan := by
  intro address outside
  have writesAway : address ∉ (Move.writes plan hole ordinal).map Prod.fst := by
    simp only [Move.writes, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨outside .order _ (by change 8 * ordinal < 8 * plan.capacity; omega),
      outside .position _ (by change 8 * hole < 8 * plan.capacity; omega)⟩
  rw [Move.memory, WordWrites.write_away _ _ _ writesAway, Move.copiedMemory, MemoryModel.copiedValueMemory,
    MemoryModel.valueMemory, scaled_cell plan .values (BitVec.ofNat 64 hole) 8]
  have holeNat : (BitVec.ofNat 64 hole).toNat = hole := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans holeInside (capacity_small kind plan valid))]
  rw [holeNat, StoreWord.put, if_neg (outside .values _ (by change hole * 8 < 8 * plan.capacity; omega))]
  apply CopyGeneral.resultMemory_away
  intro offset inside
  have vectorInside : (BitVec.ofNat 64 hole).toNat < plan.capacity := by rw [holeNat]; exact holeInside
  have extent := slot_inside kind plan hole offset holeInside inside
  constructor
  · rw [slot_byte, holeNat]
    exact outside .keys _ extent
  · rw [slot_byte, holeNat, byte_cell kind plan valid .keys _ extent]
    exact outside .keys _ (by omega)

theorem Finish.footprint (input : WordWrites.Memory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (count : Nat) (deleted : Fin count) (entries : Fin count → Nat) (hole : Nat)
    (room : count < plan.capacity) (holeInside : hole < plan.capacity)
    (activeInside : ∀ index, index ≠ deleted → entries index < plan.capacity) :
    TableFootprint.Frame input (Finish.memory input plan deleted entries hole) kind plan := by
  intro address outside
  have countAway := outside .header 24 (by change 24 < 72; decide)
  have writesAway : address ∉ (Finish.writes plan deleted entries).map Prod.fst := by
    by_cases last : deleted.val = count - 1
    · simpa only [Finish.writes, if_pos last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] using countAway
    · have ordinalInside := Nat.lt_trans deleted.isLt room
      have slotInside := activeInside (Finish.lastOrdinal deleted) (Finish.last_active deleted last)
      simp only [Finish.writes, if_neg last, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, not_or]
      exact ⟨outside .order _ (by change 8 * deleted.val < 8 * plan.capacity; omega),
        outside .position _ (by change 8 * entries (Finish.lastOrdinal deleted) < 8 * plan.capacity; omega), countAway⟩
  rw [Finish.memory, WordWrites.write_away _ _ _ writesAway, Finish.clearedMemory, ByteStore.write, StoreWord.put]
  have usedInside := used_offset_inside kind plan hole holeInside
  have away : address ≠ panByteAlignHOL (width := 64) (cell plan .used 0 + BitVec.ofNat 64 hole) := by
    rw [constant_cell, byte_cell kind plan valid .used hole usedInside]
    exact outside .used _ (by omega)
  exact if_neg away

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.Move.footprint
#print axioms InitECandidate.Solver.MutableTable.Delete.Finish.footprint
