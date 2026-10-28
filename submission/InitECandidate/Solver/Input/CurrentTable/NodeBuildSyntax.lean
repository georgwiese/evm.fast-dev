import InitECandidate.Solver.Input.OriginalEntry
import InitECandidate.Solver.Input.OriginalCode
import InitECandidate.Solver.ConstructorSyntax

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_nodedb_build with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL) := [(ofString "slice_arr",.one),(ofString "n",.one)]
def afterCap : ProgHOL 64 := match body with | .dec _ _ _ rest=>rest | _=>.skip
def allocatedTail : ProgHOL 64 := match afterCap with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
/-- The capacity loop is literally unchanged, although the current table
constructor and insertion functions now use Patricia nodes. -/
theorem body_shape : body=.dec (ofString "cap") .one (.const 4#64) (.seq WitnessRadix.Constructor.capacityLoop allocatedTail) := by
  simp only [body,afterCap,allocatedTail,Guest.Software.guestFn_nodedb_build,WitnessRadix.Constructor.capacityLoop,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,WitnessRadix.QueryBranch.localVar,Option.map_none]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "nodedb_build")=some (formals,body,.one) := by
  have checked:=OriginalCode.indexed code installed 227 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_nodedb_build) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_nodedb_build,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.body_shape
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.original_code
