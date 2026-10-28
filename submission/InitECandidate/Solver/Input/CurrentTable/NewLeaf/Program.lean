import InitECandidate.Solver.Input.CurrentTable.NewNode.Program
import InitECandidate.Solver.Input.CurrentTable.NodeStores

namespace InitECandidate.Solver.Input.CurrentTable.NewLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_new_leaf with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)]
def afterNode : ProgHOL 64 := match body with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterLength : ProgHOL 64 := match afterNode with | .dec _ _ _ rest => rest | _ => .skip
def copyPhase : ProgHOL 64 := match afterLength with | .dec _ _ _ rest => rest | _ => .skip
def afterCopy : ProgHOL 64 := match copyPhase with | .seq _ rest => rest | _ => .skip
def stores : ProgHOL 64 := match afterCopy with | .dec _ _ _ rest => rest | _ => .skip
def afterParent : ProgHOL 64 := match stores with | .seq _ rest => rest | _ => .skip
def afterValue : ProgHOL 64 := match afterParent with | .seq _ rest => rest | _ => .skip
def afterPosition : ProgHOL 64 := match afterValue with | .dec _ _ _ rest => rest | _ => .skip
def afterPositionStore : ProgHOL 64 := match afterPosition with | .seq _ rest => rest | _ => .skip
def afterMarker : ProgHOL 64 := match afterPositionStore with | .seq _ rest => rest | _ => .skip
def afterOrder : ProgHOL 64 := match afterMarker with | .seq _ rest => rest | _ => .skip
def copyArguments : List (ExpHOL 64) :=
  [.op .add [.load .one (NewNode.address 32),.panop .mul [localVar "n",localVar "stride"]],localVar "key",localVar "klen"]
def orderAddress : ExpHOL 64 := .op .add [.load .one (NewNode.address 48),.panop .mul [localVar "pos",.const 8#64]]

set_option maxRecDepth 100000 in
theorem shapes :
    body = .decCall (ofString "n") .one (ofString "htab_new_node") [localVar "t"] afterNode ∧
    afterNode = .dec (ofString "klen") .one (.load .one (NewNode.address 0)) afterLength ∧
    afterLength = .dec (ofString "stride") .one (.load .one (NewNode.address 8)) copyPhase ∧
    copyPhase = .seq (.call (some (none,none)) (ofString "memcpy") copyArguments) afterCopy ∧
    afterCopy = .dec (ofString "nodes") .one (.load .one (NewNode.address 40)) stores ∧
    stores = .seq (.store (nodeAddress 0) (.const 0#64)) afterParent ∧
    afterParent = .seq (.store (nodeAddress 8) (localVar "value")) afterValue ∧
    afterValue = .dec (ofString "pos") .one (.load .one (NewNode.address 24)) afterPosition ∧
    afterPosition = .seq (.store (nodeAddress 16) (localVar "pos")) afterPositionStore ∧
    afterPositionStore = .seq (.store (nodeAddress 24) (.panop .mul [localVar "klen",.const 8#64])) afterMarker ∧
    afterMarker = .seq (.store orderAddress (localVar "n")) afterOrder ∧
    afterOrder = .seq (.store (NewNode.address 24) (.op .add [localVar "pos",.const 1#64])) (.return (localVar "n")) := by
  simp only [body,afterNode,afterLength,copyPhase,afterCopy,stores,afterParent,afterValue,afterPosition,
    afterPositionStore,afterMarker,afterOrder,copyArguments,orderAddress,nodeAddress,NewNode.address,
    Guest.Software.guestFn_htab_new_leaf,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Scalar.plus,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_new_leaf") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 123
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_new_leaf) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_new_leaf,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.NewLeaf

#print axioms InitECandidate.Solver.Input.CurrentTable.NewLeaf.original_code
