import InitECandidate.Solver.WitnessRadix.StoreWord
import InitECandidate.Solver.WitnessRadix.Model

namespace InitECandidate.Solver.WitnessRadix.WordWrites
open Flapjack

abbrev Memory := BitVec 64 → HolWordLab 64
def write (memory : Memory) : List (BitVec 64 × BitVec 64) → Memory
  | [] => memory
  | (address, value) :: rest => write (StoreWord.put memory address value) rest

theorem lastValue_absent (input : List (BitVec 64 × BitVec 64)) (query : BitVec 64)
    (absent : ∀ entry ∈ input, entry.1 ≠ query) : lastValue query input = none := by
  induction input with
  | nil => rfl
  | cons entry rest ih =>
      have notHead := absent entry (by simp)
      have tail := ih (by intro next member; exact absent next (List.mem_cons_of_mem entry member))
      rw [lastValue, tail]
      simp [notHead]

/-- Arbitrary concrete word stores have exactly last-write-wins semantics,
including repeated destinations, and a complete untouched-memory frame. -/
theorem write_at (memory : Memory) (input : List (BitVec 64 × BitVec 64)) (query : BitVec 64) :
    write memory input query =
      match lastValue query input with | none => memory query | some value => .word value := by
  induction input generalizing memory with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨address, value⟩ := entry
      have step : lastValue query ((address, value) :: rest) =
          (match lastValue query rest with
           | some found => some found
           | none => if address = query then some value else none) := by
        rw [lastValue]
        cases lastValue query rest <;> by_cases same : address = query <;> simp [same]
      rw [write, ih, step]
      cases found : lastValue query rest with
      | none =>
          by_cases same : address = query
          · subst address
            simp [found, StoreWord.put]
          · simp [found, StoreWord.put, same, Ne.symm same]
      | some value => simp [found]

theorem write_away (memory : Memory) (input : List (BitVec 64 × BitVec 64)) (query : BitVec 64)
    (absent : query ∉ input.map Prod.fst) : write memory input query = memory query := by
  rw [write_at, lastValue_absent input query]
  intro entry member same
  exact absent (List.mem_map.mpr ⟨entry, member, same⟩)

theorem lastValue_unique (input : List (BitVec 64 × BitVec 64)) (entry : BitVec 64 × BitVec 64)
    (distinct : (input.map Prod.fst).Nodup) (member : entry ∈ input) :
    lastValue entry.1 input = some entry.2 := by
  induction input with
  | nil => simp at member
  | cons head rest ih =>
      have noDup : head.1 ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using distinct
      rcases List.mem_cons.mp member with same | tail
      · subst head
        have absent : lastValue entry.1 rest = none := by
          apply lastValue_absent
          intro next member equal
          exact noDup.1 (List.mem_map.mpr ⟨next, member, equal⟩)
        rw [lastValue, absent]
        simp
      · rw [lastValue, ih noDup.2 tail]

theorem write_unique (memory : Memory) (input : List (BitVec 64 × BitVec 64))
    (entry : BitVec 64 × BitVec 64) (distinct : (input.map Prod.fst).Nodup) (member : entry ∈ input) :
    write memory input entry.1 = .word entry.2 := by
  rw [write_at, lastValue_unique input entry distinct member]

end InitECandidate.Solver.WitnessRadix.WordWrites

#print axioms InitECandidate.Solver.WitnessRadix.WordWrites.write_at
#print axioms InitECandidate.Solver.WitnessRadix.WordWrites.write_unique
