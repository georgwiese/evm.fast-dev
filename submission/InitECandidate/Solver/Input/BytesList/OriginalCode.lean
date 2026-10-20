import InitECandidate.Solver.Input.BytesList.Program
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Installed literal original decode_bytes_list191, with its real ABI. -/
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "decode_bytes_list") = some (formals,body,VarList.returnShape) := by
  have checked := OriginalCode.indexed code installed 191 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_decode_bytes_list) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,VarList.returnShape,Guest.guestFn_decode_bytes_list,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.original_code
