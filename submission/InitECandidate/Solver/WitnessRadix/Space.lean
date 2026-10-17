import InitECandidate.Solver.WitnessRadix.Compact

namespace InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

/-- Every retained branch has two nonempty children. -/
def Full : Index Key Value → Prop
  | .empty | .bucket _ => True
  | .branch _ zero one => Full zero ∧ Full one ∧ zero ≠ .empty ∧ one ≠ .empty

theorem full_join (position : Nat) (zero one : Index Key Value)
    (left : Full zero) (right : Full one) : Full (join position zero one) := by
  cases zero <;> cases one <;> simp_all [join, Full]

theorem full_build (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) : Full (build bit position fuel input) := by
  induction fuel generalizing position input with
  | zero => cases input <;> trivial
  | succ fuel ih =>
      cases input with
      | nil => trivial
      | cons entry rest =>
          change Full (join position _ _)
          exact full_join _ _ _ (ih _ _) (ih _ _)

def branches : Index Key Value → Nat
  | .empty | .bucket _ => 0
  | .branch _ zero one => 1 + branches zero + branches one

def nonemptyCredit : Index Key Value → Nat
  | .empty => 0
  | .bucket _ | .branch _ _ _ => 1

theorem nonemptyCredit_eq_one (index : Index Key Value) (present : index ≠ .empty) :
    nonemptyCredit index = 1 := by
  cases index <;> simp_all [nonemptyCredit]

/-- A full compressed binary index has precisely one fewer branch than leaves,
unless empty. -/
theorem branches_and_leaves (index : Index Key Value) (valid : Full index) :
    branches index + nonemptyCredit index = leaves index := by
  induction index with
  | empty | bucket => rfl
  | branch position zero one ihZero ihOne =>
      obtain ⟨left, right, zeroPresent, onePresent⟩ := valid
      have hzero := ihZero left
      have hone := ihOne right
      rw [nonemptyCredit_eq_one zero zeroPresent] at hzero
      rw [nonemptyCredit_eq_one one onePresent] at hone
      simp only [branches, nonemptyCredit, leaves]
      omega

theorem branches_build (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) : branches (build bit position fuel input) ≤ input.length := by
  have full := full_build bit position fuel input
  have counted := branches_and_leaves (build bit position fuel input) full
  have bounded := leaves_build bit position fuel input
  omega

def compactBranches : CompactIndex Key Value → Nat
  | .empty | .leaf _ _ => 0
  | .branch _ zero one => 1 + compactBranches zero + compactBranches one

theorem compactBranches_eq (index : Index Key Value) :
    compactBranches (compact index) = branches index := by
  induction index with
  | empty => rfl
  | bucket input => cases h : input.getLast? <;> simp [compact, h, compactBranches, branches]
  | branch position zero one ihZero ihOne => simp [compact, compactBranches, branches, *]

theorem branches_buildIndex (bit : Key → Nat → Bool) (width : Nat)
    (input : List (Key × Value)) : compactBranches (buildIndex bit width input) ≤ input.length := by
  rw [buildIndex, compactBranches_eq]
  exact branches_build bit 0 width input

/-- Planned backing-array layout: N 32-byte hashes followed by 24-byte branch
records. Both fit inside the baseline's cap*32-byte key allocation. This proves
size arithmetic only; actual address separation/refinement is still required. -/
theorem key_pool_fits (records capacity innerNodes : Nat)
    (room : 2 * records + 2 ≤ capacity) (nodes : innerNodes ≤ records) :
    32 * records + 24 * innerNodes ≤ 32 * capacity := by
  omega

/-- Each original insertion-order array can hold a complete stable-partition
index buffer, retaining the original allocation sizes and order. -/
theorem partition_buffers_fit (records capacity : Nat) (room : 2 * records + 2 ≤ capacity) :
    8 * records ≤ 8 * capacity := by omega

theorem buildIndex_key_pool_fits (bit : Key → Nat → Bool) (width : Nat)
    (input : List (Key × Value)) (capacity : Nat) (room : 2 * input.length + 2 ≤ capacity) :
    32 * input.length + 24 * compactBranches (buildIndex bit width input) ≤ 32 * capacity :=
  key_pool_fits input.length capacity _ room (branches_buildIndex bit width input)

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.branches_buildIndex
#print axioms InitECandidate.Solver.WitnessRadix.buildIndex_key_pool_fits
#print axioms InitECandidate.Solver.WitnessRadix.partition_buffers_fit
