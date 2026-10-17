import InitECandidate.Solver.WitnessRadix.CopyIntervals
import InitECandidate.Solver.WitnessRadix.ScatterPartition

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack

def partition (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) : List (BitVec 64) :=
  (input.filter fun ordinal => !keep keyFor position ordinal) ++ input.filter (keep keyFor position)

theorem zero_one_sum (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) :
    zeros keyFor position input + ones keyFor position input = input.length := by
  induction input with
  | nil => rfl
  | cons ordinal rest ih =>
      cases selected : keep keyFor position ordinal <;>
        simp [zeros, ones, List.filter_cons, selected] at ih ⊢ <;> omega

theorem partition_length (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) :
    (partition keyFor position input).length = input.length := by
  simpa only [partition, List.length_append, zeros, ones] using zero_one_sum keyFor position input

theorem partition_memory (memory : BitVec 64 → HolWordLab 64) (dst : BitVec 64) (start : Nat)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64)) (small : start < 2 ^ 64) :
    BuildCopy.copyMemory
      (BuildCopy.copyMemory memory dst 0#64 start (input.filter fun ordinal => !keep keyFor position ordinal))
      dst 0#64 (start + zeros keyFor position input) (input.filter (keep keyFor position)) =
      BuildCopy.copyMemory memory dst (BitVec.ofNat 64 start) 0 (partition keyFor position input) := by
  unfold zeros
  rw [BuildCopy.copyMemory_append]
  exact (BuildCopy.copyMemory_start memory dst start _ small).symm

theorem row_start (base : BitVec 64) (start index : Nat) (small : start < 2 ^ 64) :
    BuildCopy.row base (BitVec.ofNat 64 start) (BitVec.ofNat 64 index) = wordAddress base (start + index) := by
  rw [BuildCopy.row_shift, BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, ← BuildCopy.wordAddress_row]

theorem partition_cross (dst : BitVec 64) (start limit : Nat)
    (keyFor : BitVec 64 → ByteKeys.Key) (position : Nat) (input : List (BitVec 64))
    (fits : start + input.length ≤ limit) (allocation : dst.toNat + 8 * limit < 2 ^ 64) :
    ∀ i < zeros keyFor position input, ∀ j < ones keyFor position input,
      wordAddress dst (start + i) ≠ wordAddress dst (start + zeros keyFor position input + j) := by
  intro i iz j jo
  have count := zero_one_sum keyFor position input
  apply BuildCopy.wordAddress_ne dst limit <;> omega

/-- The two contiguous stable-scatter blocks form the complete readable
backup array consumed by the actual copy loop. -/
theorem backup_rows (memory : BitVec 64 → HolWordLab 64) (domain : BitVec 64 → Prop)
    (dst : BitVec 64) (start limit : Nat) (keyFor : BitVec 64 → ByteKeys.Key)
    (position : Nat) (input : List (BitVec 64))
    (fits : start + input.length ≤ limit) (allocation : dst.toNat + 8 * limit < 2 ^ 64)
    (mapped : ∀ cursor < limit, domain (wordAddress dst cursor)) :
    BuildCopy.Rows
      (BuildCopy.copyMemory
        (BuildCopy.copyMemory memory dst 0#64 start (input.filter fun ordinal => !keep keyFor position ordinal))
        dst 0#64 (start + zeros keyFor position input) (input.filter (keep keyFor position)))
      domain dst (BitVec.ofNat 64 start) 0 (partition keyFor position input) := by
  have small : start < 2 ^ 64 := by omega
  rw [partition_memory memory dst start keyFor position input small]
  apply BuildCopy.copied_rows
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, Nat.add_zero, partition_length]
    omega
  · intro offset inside
    simp only [Nat.zero_add]
    rw [row_start dst start offset small]
    apply mapped
    rw [partition_length] at inside
    omega

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.partition_cross
#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.backup_rows
