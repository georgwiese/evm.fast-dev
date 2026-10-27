import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.FixedList.Program
import InitECandidate.Solver.Input.VarList.Environment
import InitECandidate.Solver.Input.OffsetsProgram

namespace InitECandidate.Solver.Input.DecoderRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem division_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "udivmod") = some (UDivMod.formals,UDivMod.body,UDivMod.returnShape) := by
  have checked := OriginalCode.indexed code installed 28 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_udivmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,UDivMod.formals,UDivMod.body,UDivMod.returnShape,Guest.Software.guestFn_udivmod,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem var_list_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_split_var_list") = some (VarList.formals,VarList.body,VarList.returnShape) := by
  have checked := OriginalCode.indexed code installed 185 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ssz_split_var_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,VarList.formals,VarList.body,VarList.returnShape,Guest.Software.guestFn_ssz_split_var_list,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem fixed_list_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_fixed_list_count") = some (FixedList.formals,FixedList.body,.one) := by
  have checked := OriginalCode.indexed code installed 186 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ssz_fixed_list_count) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,FixedList.formals,FixedList.body,Guest.Software.guestFn_ssz_fixed_list_count,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Current parser entries, independent of the old whole-main proof imports. -/
theorem fail_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_fail") = some (SszFail.formals, SszFail.body, .one) := by
  have checked := OriginalCode.indexed code installed 179 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ssz_fail) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, SszFail.formals, SszFail.body,
    Guest.Software.guestFn_ssz_fail, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

theorem offsets_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_check_offsets") = some (Offsets.formals, Offsets.body, .one) := by
  have checked := OriginalCode.indexed code installed 184 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_ssz_check_offsets) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry, declToHOL, funDeclToHOL, Offsets.formals, Offsets.body,
    Guest.Software.guestFn_ssz_check_offsets, shapeToHOL, paramToHOL, List.map_cons, List.map_nil] using checked

end InitECandidate.Solver.Input.DecoderRuntime

#print axioms InitECandidate.Solver.Input.DecoderRuntime.division_code
#print axioms InitECandidate.Solver.Input.DecoderRuntime.var_list_code
#print axioms InitECandidate.Solver.Input.DecoderRuntime.fixed_list_code

#print axioms InitECandidate.Solver.Input.DecoderRuntime.fail_code
#print axioms InitECandidate.Solver.Input.DecoderRuntime.offsets_code
