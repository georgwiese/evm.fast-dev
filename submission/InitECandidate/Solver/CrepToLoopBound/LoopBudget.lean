import InitECandidate.Solver.CrepToLoopBound.Budget

namespace InitECandidate.Solver.CrepToLoopBound

theorem recursiveBudget (rate initial middle final prefixExtra body tail conditionCost bodyCost tailCost : Nat)
    (nonzero : initial ≠ 0) (bodyDecrease : middle ≤ initial - 1) (tailDecrease : final ≤ middle)
    (prefixBound : prefixExtra ≤ conditionCost)
    (bodyBound : body ≤ rate * ((initial - 1) - middle) + bodyCost)
    (tailBound : tail ≤ rate * (middle - final) + tailCost)
    (localBound : conditionCost + bodyCost ≤ rate) :
    prefixExtra + (body + tail) ≤ rate * (initial - final) + tailCost := by
  have splitSpend : initial - final = ((initial - 1) - middle) + (middle - final) + 1 := by omega
  rw [splitSpend, Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

theorem prefixConsumeBudget (rate initial final prefixExtra body conditionCost bodyCost : Nat)
    (nonzero : initial ≠ 0) (decrease : final ≤ initial - 1)
    (prefixBound : prefixExtra ≤ conditionCost)
    (bodyBound : body ≤ rate * ((initial - 1) - final) + bodyCost)
    (localBound : conditionCost + bodyCost ≤ rate) :
    prefixExtra + body ≤ rate * (initial - final) := by
  have splitSpend : initial - final = ((initial - 1) - final) + 1 := by omega
  rw [splitSpend, Nat.mul_add, Nat.mul_one]
  omega

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.recursiveBudget
#print axioms InitECandidate.Solver.CrepToLoopBound.prefixConsumeBudget
