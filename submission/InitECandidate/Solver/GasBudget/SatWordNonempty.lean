import InitECandidate.Solver.GasBudget.U256MemoryValues

namespace InitECandidate.Solver.GasBudget.SatWord
open Flapjack Input.RlpWrite

theorem nonempty (words : U256Value.Words) (positive : resultWord words ≠ 0#64) : U256Zero.resultWord words = 0#64 := by
  by_cases zero : U256Zero.mixed words = 0#64
  · have leaves := (U256Zero.mixed_zero words).mp zero
    have scalar : resultWord words = 0#64 := by simp [resultWord, high, leaves]; rfl
    exact (positive scalar).elim
  · simp [U256Zero.resultWord, zero]

end InitECandidate.Solver.GasBudget.SatWord

#print axioms InitECandidate.Solver.GasBudget.SatWord.nonempty
