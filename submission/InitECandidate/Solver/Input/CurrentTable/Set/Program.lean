import InitECandidate.Solver.Input.CurrentTable.FindLeaf.KeyBranch

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def body : ProgHOL 64 := match Guest.Software.guestFn_htab_set with | .function fn => progToHOL fn.body | _ => .skip
def formals : List (MlS × ShapeHOL) := [(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)]
def afterLength : ProgHOL 64 := match body with | .dec _ _ _ rest => rest | _ => .skip
def afterStride : ProgHOL 64 := match afterLength with | .dec _ _ _ rest => rest | _ => .skip
def afterLeaf : ProgHOL 64 := match afterStride with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterKeys : ProgHOL 64 := match afterLeaf with | .dec _ _ _ rest => rest | _ => .skip
def emptyGuard : ProgHOL 64 := match afterKeys with | .seq first _ => first | _ => .skip
def compareCall : ProgHOL 64 := match afterKeys with | .seq _ rest => rest | _ => .skip
def afterCompare : ProgHOL 64 := match compareCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def updateGuard : ProgHOL 64 := match afterCompare with | .seq first _ => first | _ => .skip
def differenceCall : ProgHOL 64 := match afterCompare with | .seq _ rest => rest | _ => .skip
def afterDifference : ProgHOL 64 := match differenceCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def afterNodes : ProgHOL 64 := match afterDifference with | .dec _ _ _ rest => rest | _ => .skip
def afterParent : ProgHOL 64 := match afterNodes with | .dec _ _ _ rest => rest | _ => .skip
def afterNode : ProgHOL 64 := match afterParent with | .dec _ _ _ rest => rest | _ => .skip
def seek : ProgHOL 64 := match afterNode with | .seq first _ => first | _ => .skip
def newLeafCall : ProgHOL 64 := match afterNode with | .seq _ rest => rest | _ => .skip
def seekStep : ProgHOL 64 := match seek with | .while _ rest => rest | _ => .skip
def afterBit : ProgHOL 64 := match seekStep with | .dec _ _ _ rest => rest | _ => .skip

def stopGuard : ProgHOL 64 := .ite (.cmp .notLower (localVar "b") (localVar "d")) .break .skip
def setParent : ProgHOL 64 := .assign .local (ofString "p") (localVar "n")

set_option maxRecDepth 100000 in
theorem seek_shapes :
    afterNode = .seq seek newLeafCall ∧ seek = .while FindLeaf.test seekStep ∧
    seekStep = .dec (ofString "b") .one (.load .one (FindLeaf.address 24)) afterBit ∧
    afterBit = .seq stopGuard (.seq setParent FindLeaf.branch) := by
  simp only [body,afterLength,afterStride,afterLeaf,afterKeys,compareCall,afterCompare,differenceCall,
    afterDifference,afterNodes,afterParent,afterNode,seek,newLeafCall,seekStep,afterBit,stopGuard,setParent,
    FindLeaf.test,FindLeaf.address,FindLeaf.branch,FindLeaf.afterBit,FindLeaf.step,FindLeaf.loop,
    FindLeaf.afterRoot,FindLeaf.afterNodes,FindLeaf.afterBits,FindLeaf.body,
    Guest.Software.guestFn_htab_set,Guest.Software.guestFn_htab_find_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem entry_shapes :
    body = .dec (ofString "klen") .one (.load .one (.op .add [localVar "t",.const 0#64])) afterLength ∧
    afterLength = .dec (ofString "stride") .one (.load .one (.op .add [localVar "t",.const 8#64])) afterStride ∧
    afterStride = .decCall (ofString "leaf") .one (ofString "htab_find_leaf") [localVar "t",localVar "key"] afterLeaf ∧
    afterLeaf = .dec (ofString "keys") .one (.load .one (.op .add [localVar "t",.const 32#64])) afterKeys ∧
    afterKeys = .seq emptyGuard compareCall ∧ afterCompare = .seq updateGuard differenceCall ∧
    differenceCall = .decCall (ofString "d") .one (ofString "htab_first_diff")
      [localVar "key",.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "klen"] afterDifference := by
  simp only [body,afterLength,afterStride,afterLeaf,afterKeys,emptyGuard,compareCall,afterCompare,updateGuard,differenceCall,
    afterDifference,Guest.Software.guestFn_htab_set,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : OriginalCode.Installed code) :
    code.lookup (ofString "htab_set") = some (formals,body,.one) := by
  have checked := OriginalCode.indexed code installed 126
    (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn_htab_set) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,
    Guest.Software.guestFn_htab_set,shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.seek_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.entry_shapes
#print axioms InitECandidate.Solver.Input.CurrentTable.Set.original_code
