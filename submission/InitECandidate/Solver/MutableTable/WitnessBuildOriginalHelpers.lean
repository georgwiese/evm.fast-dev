import InitECandidate.Solver.MutableTable.WitnessBuildCallProgram
import InitECandidate.Solver.WitnessRadix.KeccakOriginalEnvironment
import InitECandidate.Solver.WitnessRadix.CopyGeneralCode

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Original helper entries used by the unchanged witness constructor. -/
structure OriginalHelpers (code : HolFiniteMapExact MlS (List (MlS×ShapeHOL)×ProgHOL 64×ShapeHOL)) : Prop where
  tableCode : code.lookup (ofString "htab_new")=some (TableNew.formals,TableNew.body,.one)
  hashCode : code.lookup (ofString "htab_hash")=some (Hash.formals,Hash.body,.one)
  findCode : code.lookup (ofString "htab_find_slot")=some (Find.formals,Find.body,.one)
  insertCode : code.lookup (ofString "htab_insert_raw")=some (TableCall.formals,Insert.body,.one)
  setCode : code.lookup (ofString "htab_set")=some (TableCall.formals,Set.body,.one)
  compareCode : code.lookup (ofString "memeq")=some (Memeq32.formals,Memeq32.body,.one)

set_option maxRecDepth 100000 in
theorem original_helpers (code) (installed : Input.OriginalCode.Installed code) : OriginalHelpers code := by
  constructor
  · have checked:=Input.OriginalCode.indexed code installed 116 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_new) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,TableNew.formals,TableNew.body,Guest.guestFn_htab_new,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked:=Input.OriginalCode.indexed code installed 118 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_hash) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Hash.formals,Hash.body,Guest.guestFn_htab_hash,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked:=Input.OriginalCode.indexed code installed 119 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_find_slot) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Find.formals,Find.body,Guest.guestFn_htab_find_slot,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked:=Input.OriginalCode.indexed code installed 122 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_insert_raw) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,TableCall.formals,Insert.body,Guest.guestFn_htab_insert_raw,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked:=Input.OriginalCode.indexed code installed 124 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_htab_set) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,TableCall.formals,Set.body,Guest.guestFn_htab_set,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked
  · have checked:=Input.OriginalCode.indexed code installed 13 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn_memeq) (by rfl)
    simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,Memeq32.formals,Memeq32.body,Guest.guestFn_memeq,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.original_helpers
