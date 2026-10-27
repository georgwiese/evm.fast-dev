import InitECandidate.Solver.Input.HostInputProgram
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.HostPrecheck
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString GasBudget.OriginalCodeEnvironment

set_option maxRecDepth 100000

theorem byte_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "host_input_byte") = some (Byte.formals, Byte.body, .one) := by
  have found := OriginalCode.indexed code installed 180
    (originalEntry Guest.Software.guestFn_host_input_byte) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, Byte.formals, Byte.body,
    Guest.Software.guestFn_host_input_byte, paramToHOL, shapeToHOL,
    List.map_cons, List.map_nil] using found

theorem le32_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "host_input_le32") = some (Le32.formals, Le32.body, .one) := by
  have found := OriginalCode.indexed code installed 181
    (originalEntry Guest.Software.guestFn_host_input_le32) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, Le32.formals, Le32.body,
    Guest.Software.guestFn_host_input_le32, paramToHOL, shapeToHOL,
    List.map_cons, List.map_nil] using found

end InitECandidate.Solver.Input.HostPrecheck

#print axioms InitECandidate.Solver.Input.HostPrecheck.byte_installed
#print axioms InitECandidate.Solver.Input.HostPrecheck.le32_installed
