import InitECandidate.Solver.MutableTable.WitnessBuildVariableLoop

/-! Summed costs of the unchanged constructor. These count source clocks;
transport to the baseline target evaluator remains a separate obligation. -/
namespace InitECandidate.Solver.MutableTable.WitnessBuild
open WitnessRadix

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n

def ordinalSum (index : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => index + ordinalSum (index + 1) n

def hashBlocks (slices : Nat → Graph.Slice) (index : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (slices index).2.toNat / 136 + hashBlocks slices (index + 1) n

def sliceBytes (slices : Nat → Graph.Slice) (index : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => (slices index).2.toNat + sliceBytes slices (index + 1) n

theorem ordinalSum_formula (index count : Nat) :
    ordinalSum index count = count * index + triangle count := by
  induction count generalizing index with
  | zero => simp [ordinalSum, triangle]
  | succ count ih =>
    simp only [ordinalSum, ih, triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul, Nat.succ_mul, Nat.mul_succ, Nat.succ_sub_one]
    omega

theorem triangle_double (count : Nat) : 2 * triangle count = count * (count - 1) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero => rfl
    | succ count =>
      simp only [triangle, Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul, Nat.succ_mul, Nat.mul_succ, Nat.succ_sub_one] at *
      omega

theorem budget_decompose (slices : Nat → Graph.Slice) (index count : Nat) :
    recordBudget slices index count =
      211 * count + 7 * ordinalSum index count + 20 * hashBlocks slices index count := by
  induction count generalizing index with
  | zero => rfl
  | succ count ih =>
    simp only [recordBudget, recordPrice, Keccak256.price, ordinalSum, hashBlocks, ih,
      Nat.mul_add, Nat.mul_succ]
    omega

theorem hashBlocks_bytes (slices : Nat → Graph.Slice) (index count : Nat) :
    136 * hashBlocks slices index count ≤ sliceBytes slices index count := by
  induction count generalizing index with
  | zero => simp [hashBlocks, sliceBytes]
  | succ count ih =>
    have current := Nat.div_mul_le_self (slices index).2.toNat 136
    have rest := ih (index + 1)
    simp only [hashBlocks, sliceBytes, Nat.mul_add]
    omega

theorem budget_bytes (slices : Nat → Graph.Slice) (index count : Nat) :
    recordBudget slices index count ≤ 211 * count + 7 * (count * index + triangle count) +
      20 * (sliceBytes slices index count / 136) := by
  rw [budget_decompose, ordinalSum_formula]
  have bound := hashBlocks_bytes slices index count
  have divided : hashBlocks slices index count ≤ sliceBytes slices index count / 136 := by
    omega
  omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.ordinalSum_formula
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.triangle_double
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.budget_decompose
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.hashBlocks_bytes
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.budget_bytes
