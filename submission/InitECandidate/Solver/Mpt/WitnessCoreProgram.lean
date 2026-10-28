import InitECandidate.Solver.Mpt.WitnessStepProgram

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64 := match Guest.Software.guestFn__decode_witness_node_body with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := WitnessStep.formals

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_decode_witness_node_body")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 236 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__decode_witness_node_body) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,WitnessStep.formals,body,Guest.Software.guestFn__decode_witness_node_body,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.original_code
