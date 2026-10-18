import InitECandidate.Solver.MutableTable.DeleteInitial
import InitECandidate.Solver.MutableTable.MaskedPath

namespace InitECandidate.Solver.MutableTable.Delete
open Flapjack PanSemStateFiniteExact WitnessRadix NaturalLayout

/-- The moving hole is the initial slot or a previously scanned slot. -/
def Frontier (capacity start cursor hole : Nat) : Prop :=
  ∃ rank ≤ cursor, hole = Probe.slot capacity start rank

theorem frontier_initial (capacity start : Nat) (inside : start < capacity) : Frontier capacity start 0 start := by
  exact ⟨0, Nat.le_refl _, by simp [Probe.slot, Nat.mod_eq_of_lt inside]⟩

/-- Before a full masked cycle, the next slot cannot be the moving hole. -/
theorem frontier_next_different (capacity start cursor hole : Nat) (positive : 0 < capacity)
    (startInside : start < capacity) (nextInside : cursor + 1 < capacity) (frontier : Frontier capacity start cursor hole) :
    Probe.slot capacity start (cursor + 1) ≠ hole := by
  obtain ⟨rank, earlier, holeAt⟩ := frontier
  intro same
  rw [holeAt] at same
  have repeated := Probe.slot_injective capacity start (cursor + 1) rank positive startInside nextInside (by omega) same
  omega

theorem frontier_after_choice (capacity start cursor hole nextHole : Nat) (frontier : Frontier capacity start cursor hole)
    (choice : nextHole = hole ∨ nextHole = Probe.slot capacity start (cursor + 1)) : Frontier capacity start (cursor + 1) nextHole := by
  rcases choice with rfl | rfl
  · obtain ⟨rank, earlier, same⟩ := frontier
    exact ⟨rank, by omega, same⟩
  · exact ⟨cursor + 1, Nat.le_refl _, rfl⟩

/-- The original used snapshot has a first empty slot after the removed
slot, within the old population. Actual shifts preserve this snapshot. -/
theorem deletion_first_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan)
    (slots : List Nat) (room : slots.length < plan.capacity) (occupied : MemoryModel.Occupied source kind plan slots) (deleted : Fin slots.length) :
    ∃ stop, 1 ≤ stop ∧ stop ≤ slots.length ∧
      Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity (slots.get deleted) stop)) = some 0 ∧
      ∀ rank < stop, Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (Probe.slot plan.capacity (slots.get deleted) rank)) = some 1 := by
  classical
  have startInside := occupied.inside _ (List.get_mem slots deleted)
  have startUsed : Find.usedByte source (parameters kind plan 0#64) (BitVec.ofNat 64 (slots.get deleted)) = some 1 := by
    simpa only [if_pos (List.get_mem slots deleted)] using occupied.used _ startInside
  obtain ⟨stop, bound, empty, used⟩ := Find.first_empty source (parameters kind plan 0#64) plan.capacity (slots.get deleted)
    (by omega) startInside slots room
    (by
      intro slot inside
      by_cases member : slot ∈ slots
      · exact Or.inr (by simpa only [if_pos member] using occupied.used slot inside)
      · exact Or.inl (by simpa only [if_neg member] using occupied.used slot inside))
    (by
      intro slot inside one
      by_contra missing
      have actual := occupied.used slot inside
      rw [if_neg missing, one] at actual
      cases actual)
  have positive : 1 ≤ stop := by
    by_contra zero
    have isZero : stop = 0 := by omega
    rw [isZero] at empty
    simp only [Probe.slot, Nat.add_zero, Nat.mod_eq_of_lt startInside, startUsed] at empty
    exact (by decide : (some (1 : UInt8)) ≠ some 0) empty
  exact ⟨stop, positive, bound, empty, used⟩

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.frontier_initial
#print axioms InitECandidate.Solver.MutableTable.Delete.frontier_next_different
#print axioms InitECandidate.Solver.MutableTable.Delete.frontier_after_choice
#print axioms InitECandidate.Solver.MutableTable.Delete.deletion_first_empty
