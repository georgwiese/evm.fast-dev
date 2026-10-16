import InitECandidate.Solver.CrepStatic.Programs
import InitECandidate.Proofs.FrontendStages.Crep.FunctionsFacts

namespace InitECandidate.Solver.CrepStatic
open Flapjack InitECandidate.Solver.CrepToLoopBound
set_option maxRecDepth 100000

theorem crepProgram_eq_outputs :
    crepProgram = InitECandidate.Proofs.FrontendStages.Crep.outputs := by rfl

theorem fixedCrepCodeSafe : CodeSafe 126
    (alistToFmapCodeExact InitECandidate.Proofs.FrontendStages.Crep.outputs) := by
  rw [← crepProgram_eq_outputs]
  exact crepCodeSafe

theorem fixedSimplifiedCrepCodeSafe {F : Type} (source : CrepSemHOLState 64 F)
    (code : source.code = alistToFmapCodeExact InitECandidate.Proofs.FrontendStages.Crep.outputs) :
    CodeSafe 126 (crepSimpMapcsHOL source).code := by
  apply codeSafe_simplify 126 source
  rw [code]
  exact fixedCrepCodeSafe

end InitECandidate.Solver.CrepStatic
#print axioms InitECandidate.Solver.CrepStatic.crepProgram_eq_outputs
#print axioms InitECandidate.Solver.CrepStatic.fixedCrepCodeSafe
#print axioms InitECandidate.Solver.CrepStatic.fixedSimplifiedCrepCodeSafe
