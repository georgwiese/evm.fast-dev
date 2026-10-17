import InitECandidate.Solver.WitnessRadix.BuildCopyPost
import InitECandidate.Solver.WitnessRadix.ScatterReady

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack

theorem rows_mapped (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) (index : Nat) (input : List (BitVec 64))
    (rows : Rows memory domain base start index input) (offset : Nat) (inside : offset < input.length) :
    domain (row base start (BitVec.ofNat 64 (index + offset))) := by
  induction input generalizing index offset with
  | nil => simp at inside
  | cons value rest ih =>
      cases offset with
      | zero => simpa only [Nat.add_zero] using rows.1
      | succ offset =>
          have next := ih (index + 1) rows.2.2 offset (by simp only [List.length_cons] at inside; omega)
          simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using next

theorem copyMemory_append (memory : BitVec 64 → HolWordLab 64) (base start : BitVec 64)
    (index : Nat) (left right : List (BitVec 64)) :
    copyMemory (copyMemory memory base start index left) base start (index + left.length) right =
      copyMemory memory base start index (left ++ right) := by
  induction left generalizing memory index with
  | nil => rfl
  | cons value rest ih =>
      have next := ih (StoreWord.put memory (row base start (BitVec.ofNat 64 index)) value) (index + 1)
      simpa only [copyMemory, List.cons_append, List.length_cons,
        Nat.add_assoc, Nat.add_comm rest.length 1] using next

theorem row_shift (base start : BitVec 64) (index : Nat) :
    row base start (BitVec.ofNat 64 index) = row base 0#64 (BitVec.ofNat 64 (start.toNat + index)) := by
  rw [row_address, row_address]
  simp

theorem copyMemory_shift (memory : BitVec 64 → HolWordLab 64) (base start : BitVec 64)
    (index : Nat) (input : List (BitVec 64)) :
    copyMemory memory base start index input = copyMemory memory base 0#64 (start.toNat + index) input := by
  induction input generalizing memory index with
  | nil => rfl
  | cons value rest ih =>
      rw [copyMemory, copyMemory, row_shift base start index, ih]
      simp only [Nat.add_assoc]

theorem copyMemory_start (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (start : Nat) (input : List (BitVec 64)) (small : start < 2 ^ 64) :
    copyMemory memory base (BitVec.ofNat 64 start) 0 input = copyMemory memory base 0#64 start input := by
  rw [copyMemory_shift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.add_zero]

theorem wordAddress_row (base : BitVec 64) (index : Nat) :
    ScatterProgram.wordAddress base index = row base 0#64 (BitVec.ofNat 64 index) := by
  simp only [ScatterProgram.wordAddress, row, BitVec.zero_add]

theorem wordAddress_ne (base : BitVec 64) (limit left right : Nat)
    (allocation : base.toNat + 8 * limit < 2 ^ 64)
    (leftInside : left < limit) (rightInside : right < limit) (different : left ≠ right) :
    ScatterProgram.wordAddress base left ≠ ScatterProgram.wordAddress base right := by
  rw [wordAddress_row, wordAddress_row]
  apply rows_injective base 0#64 limit left right
  · simpa using allocation
  · exact leftInside
  · exact rightInside
  · exact different

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copyMemory_append
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.copyMemory_start
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.wordAddress_ne
