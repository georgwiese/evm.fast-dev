import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input.ClockCost
/-- Compose a funded source caller tick with the real bounded continuation. -/
theorem funded_tick (source target price : Nat) (funded : 1≤source)
    (monotone : target≤source-1) (priced : source-1-target≤price) : source-target≤1+price := by omega
end InitECandidate.Solver.Input.ClockCost
#print axioms InitECandidate.Solver.Input.ClockCost.funded_tick
