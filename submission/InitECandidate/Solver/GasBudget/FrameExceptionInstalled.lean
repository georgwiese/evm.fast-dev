import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment
import InitECandidate.Solver.GasBudget.FrameExceptionNormalCall

namespace InitECandidate.Solver.GasBudget.FrameException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "frame_exception") = some (formals, body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[533]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_frame_exception) := by rfl
  have checked := Input.OriginalCode.indexed code installed 533 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_frame_exception,
    formals, body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

theorem original_refill_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "refill_frame_state_gas") = some ([], Refill.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[410]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_refill_frame_state_gas) := by rfl
  have checked := Input.OriginalCode.indexed code installed 410 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_refill_frame_state_gas,
    Refill.body, shapeToHOL, List.map_nil] using checked

theorem original_halt_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "frame_halt") = some (Halt.formals, Halt.body, .one) := by
  have found : (functionsHOL Input.OriginalCode.program)[540]? =
      some (OriginalCodeEnvironment.originalEntry Guest.guestFn_frame_halt) := by rfl
  have checked := Input.OriginalCode.indexed code installed 540 _ found
  simpa only [OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Guest.guestFn_frame_halt,
    Halt.formals, Halt.body, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.GasBudget.FrameException

#print axioms InitECandidate.Solver.GasBudget.FrameException.original_code
#print axioms InitECandidate.Solver.GasBudget.FrameException.original_refill_code
#print axioms InitECandidate.Solver.GasBudget.FrameException.original_halt_code
