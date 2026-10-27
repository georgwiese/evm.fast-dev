import InitECandidate.Solver.Input.OffsetsEnvironment
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

namespace InitECandidate.Solver.Input.SszCurrentCode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString GasBudget.OriginalCodeEnvironment
set_option maxRecDepth 100000

theorem fail_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one) := by
  have found := OriginalCode.indexed code installed 179
    (originalEntry Guest.Software.guestFn_ssz_fail) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, SszFail.formals, SszFail.body,
    Guest.Software.guestFn_ssz_fail, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using found

theorem offsets_installed (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals, Offsets.body, .one) := by
  have found := OriginalCode.indexed code installed 184
    (originalEntry Guest.Software.guestFn_ssz_check_offsets) (by rfl)
  simpa only [originalEntry, declToHOL, funDeclToHOL, Offsets.formals, Offsets.body,
    Guest.Software.guestFn_ssz_check_offsets, paramToHOL, shapeToHOL, List.map_cons, List.map_nil] using found

end InitECandidate.Solver.Input.SszCurrentCode

#print axioms InitECandidate.Solver.Input.SszCurrentCode.fail_installed
#print axioms InitECandidate.Solver.Input.SszCurrentCode.offsets_installed
