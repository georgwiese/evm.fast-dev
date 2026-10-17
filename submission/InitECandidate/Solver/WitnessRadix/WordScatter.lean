import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.WitnessRadix.WordScatter
open Flapjack

abbrev Memory := BitVec 64 → HolWordLab 64

def writeWords (address : Nat → BitVec 64) (memory : Memory) (start : Nat) :
    List (BitVec 64) → Memory
  | [] => memory
  | value :: rest => writeWords address (StoreWord.put memory (address start) value) (start + 1) rest

def scatterWords (address : Nat → BitVec 64) (keep : BitVec 64 → Bool) :
    List (BitVec 64) → Memory → Nat → Nat → Memory
  | [], memory, _, _ => memory
  | value :: rest, memory, zeroStart, oneStart =>
      if keep value then scatterWords address keep rest
        (StoreWord.put memory (address oneStart) value) zeroStart (oneStart + 1)
      else scatterWords address keep rest
        (StoreWord.put memory (address zeroStart) value) (zeroStart + 1) oneStart

theorem put_commute (memory : Memory) (a b x y : BitVec 64) (different : a ≠ b) :
    StoreWord.put (StoreWord.put memory a x) b y = StoreWord.put (StoreWord.put memory b y) a x := by
  funext query
  by_cases atA : query = a
  · subst query
    simp [StoreWord.put, different]
  · by_cases atB : query = b
    · subst query
      simp [StoreWord.put, Ne.symm different]
    · simp [StoreWord.put, atA, atB]

theorem writeWords_put_away (address : Nat → BitVec 64) (memory : Memory)
    (start : Nat) (input : List (BitVec 64)) (pointer value : BitVec 64)
    (away : ∀ offset < input.length, address (start + offset) ≠ pointer) :
    writeWords address (StoreWord.put memory pointer value) start input =
      StoreWord.put (writeWords address memory start input) pointer value := by
  induction input generalizing memory start with
  | nil => rfl
  | cons head rest ih =>
      have notHead := away 0 (by simp)
      simp only [Nat.add_zero] at notHead
      simp only [writeWords]
      rw [put_commute memory pointer (address start) value head (Ne.symm notHead), ih]
      intro offset inside
      have tail := away (offset + 1) (by simp only [List.length_cons]; omega)
      simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using tail

/-- Exact stable partition in actual HOL word memory. Only cross-bucket
address separation is required; the untouched memory is preserved exactly. -/
theorem scatter_eq_blocks (address : Nat → BitVec 64) (keep : BitVec 64 → Bool)
    (input : List (BitVec 64)) (memory : Memory) (zeroStart oneStart : Nat)
    (separate : ∀ i < (input.filter fun value => !keep value).length,
      ∀ j < (input.filter keep).length, address (zeroStart + i) ≠ address (oneStart + j)) :
    scatterWords address keep input memory zeroStart oneStart =
      writeWords address (writeWords address memory zeroStart (input.filter fun value => !keep value))
        oneStart (input.filter keep) := by
  induction input generalizing memory zeroStart oneStart with
  | nil => rfl
  | cons value rest ih =>
      cases bit : keep value with
      | false =>
          simp only [scatterWords, bit, Bool.false_eq_true, ↓reduceIte]
          rw [ih]
          · simp [List.filter_cons, bit, writeWords]
          · intro i inside j oneInside
            have noAlias := separate (i + 1) (by simpa [List.filter_cons, bit] using Nat.succ_lt_succ inside)
              j (by simpa [List.filter_cons, bit] using oneInside)
            simpa only [Nat.add_assoc, Nat.add_comm 1 i] using noAlias
      | true =>
          simp only [scatterWords, bit, ↓reduceIte]
          rw [ih]
          · rw [writeWords_put_away]
            · simp [List.filter_cons, bit, writeWords]
            · intro i inside
              have noAlias := separate i (by simpa [List.filter_cons, bit] using inside) 0
                (by simp [List.filter_cons, bit])
              simpa only [Nat.add_zero] using noAlias
          · intro i inside j oneInside
            have noAlias := separate i (by simpa [List.filter_cons, bit] using inside)
              (j + 1) (by simpa [List.filter_cons, bit] using Nat.succ_lt_succ oneInside)
            simpa only [Nat.add_assoc, Nat.add_comm 1 j] using noAlias

end InitECandidate.Solver.WitnessRadix.WordScatter

#print axioms InitECandidate.Solver.WitnessRadix.WordScatter.scatter_eq_blocks
