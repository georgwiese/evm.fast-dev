import InitECandidate.Solver.Input.PayloadBodyNormalPadded
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.DecoderRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem division_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "udivmod") = some (UDivMod.formals,UDivMod.body,UDivMod.returnShape) := by
  have checked := OriginalCode.indexed code installed 28 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_udivmod) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,UDivMod.formals,UDivMod.body,UDivMod.returnShape,Guest.guestFn_udivmod,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem var_list_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_split_var_list") = some (VarList.formals,VarList.body,VarList.returnShape) := by
  have checked := OriginalCode.indexed code installed 187 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ssz_split_var_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,VarList.formals,VarList.body,VarList.returnShape,Guest.guestFn_ssz_split_var_list,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

theorem fixed_list_code (code) (installed : OriginalCode.Installed code) : code.lookup (ofString "ssz_fixed_list_count") = some (FixedList.formals,FixedList.body,.one) := by
  have checked := OriginalCode.indexed code installed 188 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_ssz_fixed_list_count) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,FixedList.formals,FixedList.body,Guest.guestFn_ssz_fixed_list_count,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.DecoderRuntime

#print axioms InitECandidate.Solver.Input.DecoderRuntime.division_code
#print axioms InitECandidate.Solver.Input.DecoderRuntime.var_list_code
#print axioms InitECandidate.Solver.Input.DecoderRuntime.fixed_list_code
