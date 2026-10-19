import InitECandidate.Solver.WitnessRadix.CopyGeneralEnvironment
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.WitnessRadix.CopyGeneral
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memcpy")=some (formals,Copy32.body,.one) := by
  have checked := Input.OriginalCode.indexed code installed 11 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_memcpy) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,Copy32.body,Guest.guestFn_memcpy,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.WitnessRadix.CopyGeneral

#print axioms InitECandidate.Solver.WitnessRadix.CopyGeneral.original_code
