import InitECandidate.Solver.WordToStackBound.Budget

namespace InitECandidate.Solver.WordToStackBound

/-- A source call decrement pays for both the callee and its one selected
continuation, each with local cost at most limit. Recursive costs compose. -/
theorem callBudget (limit initial middle final bodyExtra continuationExtra bodyCost continuationCost : Nat)
    (nonzero : initial ≠ 0) (bodyDecrease : middle ≤ initial - 1)
    (continuationDecrease : final ≤ middle)
    (bodyCostBound : bodyCost ≤ limit) (continuationCostBound : continuationCost ≤ limit)
    (bodyBound : bodyExtra ≤ (2 * limit) * ((initial - 1) - middle) + bodyCost)
    (continuationBound : continuationExtra ≤ (2 * limit) * (middle - final) + continuationCost) :
    bodyExtra + continuationExtra ≤ (2 * limit) * (initial - final) := by
  apply consumeBudget (2 * limit) initial final (bodyExtra + continuationExtra)
    (bodyCost + continuationCost) nonzero (by omega) (by omega)
  exact composeBudget (2 * limit) (initial - 1) middle final bodyExtra continuationExtra
    bodyCost continuationCost bodyDecrease continuationDecrease bodyBound continuationBound

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.callBudget
