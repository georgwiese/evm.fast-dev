import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input.ClockCost
/-- Add actual spent-clock allowances along two reached monotone segments. -/
theorem spend_chain (source middle target frontPrice tail : Nat) (front : middle≤source) (back : target≤middle)
    (prefixCost : source-middle≤frontPrice) (tailCost : middle-target≤tail) : source-target≤frontPrice+tail := by omega
end InitECandidate.Solver.Input.ClockCost
#print axioms InitECandidate.Solver.Input.ClockCost.spend_chain
