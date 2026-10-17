import InitECandidate.Solver.MutableTable.PlacementBuild
import Mathlib.Data.Finset.Card

namespace InitECandidate.Solver.MutableTable.Placement

variable {Key Value : Type} [DecidableEq Key]

def keySet (input : List (Key × Value)) : Finset Key := (input.map Prod.fst).toFinset
def distinctCount (input : List (Key × Value)) : Nat := (keySet input).card

theorem distinctCount_le_length (input : List (Key × Value)) : distinctCount input ≤ input.length := by
  simpa only [distinctCount, keySet, List.length_map] using List.toFinset_card_le (input.map Prod.fst)

theorem distinctCount_snoc (input : List (Key × Value)) (key : Key) (value : Value) :
    distinctCount (input ++ [(key, value)]) =
      if key ∈ keySet input then distinctCount input else distinctCount input + 1 := by
  by_cases member : key ∈ keySet input
  · simp [distinctCount, keySet, List.toFinset_append, Finset.union_singleton,
      show key ∈ (input.map Prod.fst).toFinset from member, member]
  · simp [distinctCount, keySet, List.toFinset_append, Finset.union_singleton,
      show key ∉ (input.map Prod.fst).toFinset from member, member]

theorem lastValue_exists (input : List (Key × Value)) (key : Key) (member : key ∈ input.map Prod.fst) :
    ∃ value, WitnessRadix.lastValue key input = some value := by
  induction input with
  | nil => simp at member
  | cons entry rest ih =>
    cases tail : WitnessRadix.lastValue key rest with
    | some value => exact ⟨value, by simp only [WitnessRadix.lastValue, tail]⟩
    | none =>
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with same | earlier
      · exact ⟨entry.2, by simp only [WitnessRadix.lastValue, tail, if_pos same.symm]⟩
      · obtain ⟨value, found⟩ := ih earlier
        rw [tail] at found
        contradiction

/-- Repeated keys add no new occupied slot. The concrete table's covering
list therefore costs at most the number of distinct input keys. -/
theorem build_cover_distinct (capacity : Nat) (home : Key → Nat)
    (input : List (Key × Value)) (table : Table Key Value) (trace : Builds capacity home input table) :
    ∃ order : List Nat, order.length ≤ distinctCount input ∧
      ∀ index < capacity, table index ≠ none → index ∈ order := by
  induction trace with
  | empty => exact ⟨[], by simp [distinctCount, keySet], by intro index inside occupied; exact False.elim (occupied rfl)⟩
  | snoc input table prior index key value inside chosen only path ih =>
    obtain ⟨order, bound, covered⟩ := ih
    have size := distinctCount_snoc input key value
    by_cases old : key ∈ keySet input
    · have present : key ∈ input.map Prod.fst := List.mem_toFinset.mp old
      obtain ⟨previous, found⟩ := lastValue_exists input key present
      have invariants := build_invariants capacity home input table prior
      obtain ⟨slot, slotInside, cell⟩ := invariants.2.1.2 key previous found
      have position := only slot slotInside previous cell
      have indexCovered : index ∈ order := by
        rw [← position]
        exact covered slot slotInside (by rw [cell]; simp)
      refine ⟨order, ?_, ?_⟩
      · rw [size, if_pos old]
        exact bound
      · intro query queryInside occupied
        by_cases same : query = index
        · simpa only [same] using indexCovered
        · simp only [put, if_neg same] at occupied
          exact covered query queryInside occupied
    · refine ⟨order ++ [index], ?_, ?_⟩
      · rw [size, if_neg old, List.length_append, List.length_singleton]
        omega
      · intro query queryInside occupied
        by_cases same : query = index
        · simp [same]
        · simp only [put, if_neg same] at occupied
          exact List.mem_append_left _ (covered query queryInside occupied)

end InitECandidate.Solver.MutableTable.Placement

#print axioms InitECandidate.Solver.MutableTable.Placement.distinctCount_le_length
#print axioms InitECandidate.Solver.MutableTable.Placement.distinctCount_snoc
#print axioms InitECandidate.Solver.MutableTable.Placement.lastValue_exists
#print axioms InitECandidate.Solver.MutableTable.Placement.build_cover_distinct
