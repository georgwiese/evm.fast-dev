import InitECandidate.Solver.WitnessRadix.MemeqFormals
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.Input.OriginalEntry

/-! Current Software memeq ABI, independent of dictionary cost models.
The existing namespace is retained for current and historical clients. -/
namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 13 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_memeq) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Memeq32.body,Memeq32.formals,
    Guest.guestFn_memeq,Guest.Software.guestFn_memeq,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.original_code
