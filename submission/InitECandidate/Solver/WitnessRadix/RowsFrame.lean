import InitECandidate.Solver.WitnessRadix.CopyIntervals

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack

theorem rows_of_agreement (source target : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) (index : Nat) (input : List (BitVec 64))
    (agree : ∀ offset < input.length,
      source (row base start (BitVec.ofNat 64 (index + offset))) = target (row base start (BitVec.ofNat 64 (index + offset))))
    (rows : Rows source domain base start index input) : Rows target domain base start index input := by
  induction input generalizing index with
  | nil => trivial
  | cons value rest ih =>
      refine ⟨rows.1, ?_, ih (index + 1) ?_ rows.2.2⟩
      · have head := agree 0 (by simp)
        simp only [Nat.add_zero] at head
        exact head.symm.trans rows.2.1
      · intro offset bound
        have tail := agree (offset + 1) (by simp only [List.length_cons]; omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 offset] using tail

theorem rows_append (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base start : BitVec 64) (index : Nat) (left right : List (BitVec 64)) :
    Rows memory domain base start index (left ++ right) ↔
      Rows memory domain base start index left ∧ Rows memory domain base start (index + left.length) right := by
  induction left generalizing index with
  | nil => simp [Rows]
  | cons value rest ih =>
      simp only [List.cons_append, Rows, ih, List.length_cons]
      have offset : index + (rest.length + 1) = index + 1 + rest.length := by omega
      rw [offset]
      tauto

theorem rows_start_shift (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (base : BitVec 64) (start index : Nat) (input : List (BitVec 64)) :
    Rows memory domain base (BitVec.ofNat 64 start) index input ↔
      Rows memory domain base 0#64 (start + index) input := by
  induction input generalizing index with
  | nil => rfl
  | cons value rest ih =>
      have address : row base (BitVec.ofNat 64 start) (BitVec.ofNat 64 index) =
          row base 0#64 (BitVec.ofNat 64 (start + index)) := by
        simp only [row, BitVec.zero_add, BitVec.ofNat_add]
      simp only [Rows, address, ih, Nat.add_assoc]

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.rows_of_agreement
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.rows_append
#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.rows_start_shift
