import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The unchanged current run_attempt, including its actual payload/parent
gas checks. This syntax/entry interface imports no obsolete header contracts. -/
def body : ProgHOL 64 := match Guest.Software.guestFn_run_attempt with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "si",.one)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "run_attempt")=some (formals,body,.one) := by
  have found:=OriginalCode.indexed code installed 803
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_run_attempt) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_run_attempt,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using found

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.original_code
