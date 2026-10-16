import InitECandidate.Solver.CrepToLoopBound.Common

namespace InitECandidate.Solver.CrepToLoopBound
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

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.composeBudget
#print axioms InitECandidate.Solver.CrepToLoopBound.extendBudget
#print axioms InitECandidate.Solver.CrepToLoopBound.consumeBudget
