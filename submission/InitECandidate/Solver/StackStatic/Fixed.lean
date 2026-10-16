import InitECandidate.Solver.StackStatic.Programs
import InitECandidate.Proofs.BackendStages.Raw
import InitECandidate.Proofs.BackendStages.Alloc

namespace InitECandidate.Solver.StackStatic
open Flapjack InitECandidate.Proofs.BackendStages
set_option maxRecDepth 100000

theorem rawProgram_eq_stack : rawProgram = Raw.stack := by rfl

theorem allocProgram_eq_stack : allocProgram = Alloc.stack := by rfl

theorem fixedRawCodeSafe : InitECandidate.Solver.StackAllocBound.CodeSafe
    (sptFromAList Raw.stack) := by
  rw [← rawProgram_eq_stack]
  exact rawCodeSafe

theorem fixedAllocCodeSafe : InitECandidate.Solver.StackRemoveDirect.CodeSafe
    (sptFromAList Alloc.stack) := by
  rw [← allocProgram_eq_stack]
  exact allocCodeSafe

end InitECandidate.Solver.StackStatic
#print axioms InitECandidate.Solver.StackStatic.rawProgram_eq_stack
#print axioms InitECandidate.Solver.StackStatic.allocProgram_eq_stack
#print axioms InitECandidate.Solver.StackStatic.fixedRawCodeSafe
#print axioms InitECandidate.Solver.StackStatic.fixedAllocCodeSafe
