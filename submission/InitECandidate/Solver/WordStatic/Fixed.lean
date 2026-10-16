import InitECandidate.Solver.WordStatic.Programs
import InitECandidate.Proofs.StackAnalysis.Data

namespace InitECandidate.Solver.WordStatic
open Flapjack InitECandidate.Solver.WordToStackBound
set_option maxRecDepth 100000

theorem wordProgram_eq_outputs : wordProgram = InitECandidate.Proofs.StackAnalysis.outputs := by
  rfl

theorem fixedWordCodeSafe : CodeSafe 17 (sptFromAList InitECandidate.Proofs.StackAnalysis.outputs) := by
  rw [← wordProgram_eq_outputs]
  exact wordCodeSafe

end InitECandidate.Solver.WordStatic
#print axioms InitECandidate.Solver.WordStatic.wordProgram_eq_outputs
#print axioms InitECandidate.Solver.WordStatic.fixedWordCodeSafe
