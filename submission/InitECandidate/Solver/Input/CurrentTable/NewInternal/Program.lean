import InitECandidate.Solver.Input.CurrentTable.NewNode.Program
import InitECandidate.Solver.Input.CurrentTable.NodeStores

namespace InitECandidate.Solver.Input.CurrentTable.NewInternal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_new_internal with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t",.one),(ofString "bit",.one)]
def afterNode : ProgHOL 64 := match body with | .decCall _ _ _ _ rest => rest | _ => .skip
def stores : ProgHOL 64 := match afterNode with | .dec _ _ _ rest => rest | _ => .skip
def afterParent : ProgHOL 64 := match stores with | .seq _ rest => rest | _ => .skip
def afterLeft : ProgHOL 64 := match afterParent with | .seq _ rest => rest | _ => .skip
def afterRight : ProgHOL 64 := match afterLeft with | .seq _ rest => rest | _ => .skip

set_option maxRecDepth 100000 in
theorem shapes :
    body = .decCall (ofString "n") .one (ofString "htab_new_node") [localVar "t"] afterNode ∧
    afterNode = .dec (ofString "nodes") .one (.load .one (NewNode.address 40)) stores ∧
    stores = .seq (.store (nodeAddress 0) (.const 0#64)) afterParent ∧
    afterParent = .seq (.store (nodeAddress 8) (.const 0#64)) afterLeft ∧
    afterLeft = .seq (.store (nodeAddress 16) (.const 0#64)) afterRight ∧
    afterRight = .seq (.store (nodeAddress 24) (localVar "bit")) (.return (localVar "n")) := by
  simp only [body,afterNode,stores,afterParent,afterLeft,afterRight,nodeAddress,NewNode.address,
    Guest.Software.guestFn_htab_new_internal,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Scalar.plus,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_new_internal") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 124
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_new_internal) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_new_internal,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.NewInternal

#print axioms InitECandidate.Solver.Input.CurrentTable.NewInternal.original_code
