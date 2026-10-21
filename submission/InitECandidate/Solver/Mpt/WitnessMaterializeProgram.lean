import InitECandidate.Solver.Mpt.WitnessDecodeLookupProgram

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.guestFn__decode_witness_node with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "db",.one),(ofString "p",.one),(ofString "n",.one)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_decode_witness_node")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 240 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__decode_witness_node) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__decode_witness_node,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.original_code
