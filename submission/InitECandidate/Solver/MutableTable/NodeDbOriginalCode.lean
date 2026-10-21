import InitECandidate.Solver.MutableTable.WitnessDictionaryLookup
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.GasBudget.OriginalCodeEnvironment

namespace InitECandidate.Solver.MutableTable.NodeDb
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000

/-- Literal original getter120, used by the unchanged node database. -/
theorem original_get_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "htab_get")=some (Get.formals,Get.body,Get.pairShape) := by
  have checked:=Input.OriginalCode.indexed code installed 120 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_get) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Get.formals,Find.formals,Get.body,Get.pairShape,Guest.guestFn_htab_get,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

/-- Literal original nodedb_lookup230 and its actual triple return ABI. -/
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "nodedb_lookup")=some (formals,body,.comb [.one,.one,.one]) := by
  have checked:=Input.OriginalCode.indexed code installed 230 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_nodedb_lookup) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn_nodedb_lookup,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.MutableTable.NodeDb

#print axioms InitECandidate.Solver.MutableTable.NodeDb.original_get_code
#print axioms InitECandidate.Solver.MutableTable.NodeDb.original_code
