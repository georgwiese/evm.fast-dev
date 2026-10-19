import InitECandidate.Solver.WitnessRadix.CopyGeneral

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack

theorem cost_aligned (src dst : BitVec 64) (length : Nat) (aligned : aligned src dst) :
    cost src dst length = length / 32 + (length % 32) / 8 + length % 8 := by
  have division32 := Nat.mod_add_div length 32
  have division8 := Nat.mod_add_div (length % 32) 8
  have division := Nat.mod_add_div length 8
  have residual : length - CopyWords.prefixIndex length = length % 8 := by
    unfold CopyWords.prefixIndex
    omega
  rw [cost, if_pos aligned, CopyBytes.suffixCost, residual, CopyWords.prefixCost]
  omega

/-- The unaligned original path still copies eight bytes per main loop.
Its source-clock price is bounded using the real block and tail counts. -/
theorem cost_blocks (src dst : BitVec 64) (length : Nat) : cost src dst length ≤ length / 8 + 7 := by
  by_cases aligned : aligned src dst
  · rw [cost_aligned src dst length aligned]
    have division32 := Nat.mod_add_div length 32
    have division8 := Nat.mod_add_div (length % 32) 8
    have division := Nat.mod_add_div length 8
    omega
  · rw [cost, if_neg aligned, CopyBytes.suffixCost, Nat.sub_zero]
    omega

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.cost_aligned
#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.cost_blocks
