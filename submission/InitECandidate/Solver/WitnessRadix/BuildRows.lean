import InitECandidate.Solver.WitnessRadix.BuildCopy

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack

def Rows (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) : Nat → List (BitVec 64) → Prop
  | _, [] => True
  | index, value :: rest =>
      domain (row base start (BitVec.ofNat 64 index)) ∧
      memory (row base start (BitVec.ofNat 64 index)) = .word value ∧
      Rows memory domain base start (index + 1) rest

def copyMemory (memory : BitVec 64 → HolWordLab 64) (base start : BitVec 64) :
    Nat → List (BitVec 64) → (BitVec 64 → HolWordLab 64)
  | _, [] => memory
  | index, value :: rest =>
      copyMemory (StoreWord.put memory (row base start (BitVec.ofNat 64 index)) value)
        base start (index + 1) rest

theorem rows_store_away (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start address value : BitVec 64) (index : Nat) (input : List (BitVec 64))
    (rows : Rows memory domain base start index input)
    (away : ∀ offset < input.length, row base start (BitVec.ofNat 64 (index + offset)) ≠ address) :
    Rows (StoreWord.put memory address value) domain base start index input := by
  induction input generalizing index with
  | nil => trivial
  | cons head rest ih =>
      obtain ⟨mapped, stored, tail⟩ := rows
      have notHead := away 0 (by simp)
      simp only [Nat.add_zero] at notHead
      refine ⟨mapped, ?_, ih (index + 1) tail ?_⟩
      · simp [StoreWord.put, notHead, stored]
      · intro offset bound
        have notTail := away (offset + 1) (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using notTail

theorem copyMemory_away (memory : BitVec 64 → HolWordLab 64) (base start query : BitVec 64)
    (index : Nat) (input : List (BitVec 64))
    (away : ∀ offset < input.length, query ≠ row base start (BitVec.ofNat 64 (index + offset))) :
    copyMemory memory base start index input query = memory query := by
  induction input generalizing memory index with
  | nil => rfl
  | cons head rest ih =>
      rw [copyMemory, ih]
      · have notHead := away 0 (by simp)
        simp only [Nat.add_zero] at notHead
        exact if_neg notHead
      · intro offset bound
        have notTail := away (offset + 1) (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using notTail

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.rows_store_away
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copyMemory_away
