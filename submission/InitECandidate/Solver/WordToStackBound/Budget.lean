import InitECandidate.Solver.WordToStackBound.Common

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

theorem seqSupported {width : Nat} [NeZero width]
    {first second : WordLangProgHOL (BitVec width)}
    (supported : noInstallSubprogsHOL (.seq first second) = true) :
    noInstallSubprogsHOL first = true ∧ noInstallSubprogsHOL second = true := by
  simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp, Bool.and_eq_true] using supported

theorem composeBudget (limit initial middle final first second firstCost secondCost : Nat)
    (firstDecrease : middle ≤ initial) (secondDecrease : final ≤ middle)
    (firstBound : first ≤ limit * (initial - middle) + firstCost)
    (secondBound : second ≤ limit * (middle - final) + secondCost) :
    first + second ≤ limit * (initial - final) + (firstCost + secondCost) := by
  have splitSpend : initial - final = (initial - middle) + (middle - final) := by omega
  rw [splitSpend, Nat.mul_add]
  omega

theorem extendBudget (limit initial middle final extra firstCost secondCost : Nat)
    (decrease : final ≤ middle)
    (bound : extra ≤ limit * (initial - middle) + firstCost) :
    extra ≤ limit * (initial - final) + (firstCost + secondCost) := by
  have times := Nat.mul_le_mul_left limit (show initial - middle ≤ initial - final by omega)
  omega

theorem consumeBudget (limit initial final extra bodyCost : Nat)
    (nonzero : initial ≠ 0) (decrease : final ≤ initial - 1)
    (bodyBound : bodyCost ≤ limit)
    (bound : extra ≤ limit * ((initial - 1) - final) + bodyCost) :
    extra ≤ limit * (initial - final) := by
  have splitSpend : initial - final = ((initial - 1) - final) + 1 := by omega
  rw [splitSpend, Nat.mul_add, Nat.mul_one]
  omega

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.seqSupported
#print axioms InitECandidate.Solver.WordToStackBound.composeBudget
#print axioms InitECandidate.Solver.WordToStackBound.extendBudget
#print axioms InitECandidate.Solver.WordToStackBound.consumeBudget
