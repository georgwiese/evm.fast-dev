import InitECandidate.Solver.Input.CurrentTable.Set.Program

namespace InitECandidate.Solver.Input.CurrentTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def emptyLeafCall : ProgHOL 64 := match emptyGuard with | .ite _ yes _ => yes | _ => .skip
def emptyFinish : ProgHOL 64 := match emptyLeafCall with | .decCall _ _ _ _ rest => rest | _ => .skip
def updateBody : ProgHOL 64 := match updateGuard with | .ite _ yes _ => yes | _ => .skip

def compareArguments : List (ExpHOL 64) :=
  [.op .add [localVar "keys",.panop .mul [localVar "leaf",localVar "stride"]],localVar "key",localVar "klen"]
def leafArguments : List (ExpHOL 64) := [localVar "t",localVar "key",localVar "value"]

set_option maxRecDepth 100000 in
theorem guard_shapes :
    emptyGuard = .ite (.cmp .equal (localVar "leaf") (.const 0#64)) emptyLeafCall .skip ∧
    emptyLeafCall = .decCall (ofString "nl") .one (ofString "htab_new_leaf") leafArguments emptyFinish ∧
    emptyFinish = .seq (.store (.op .add [localVar "t",.const 56#64]) (localVar "nl")) (.return (.const 0#64)) ∧
    updateGuard = .ite (.cmp .notEqual (localVar "eq") (.const 0#64)) updateBody .skip ∧
    updateBody = .seq (.store (.op .add [.load .one (.op .add [localVar "t",.const 40#64]),
      .panop .mul [localVar "leaf",.const 32#64],.const 8#64]) (localVar "value")) (.return (.const 0#64)) ∧
    compareCall = .decCall (ofString "eq") .one (ofString "memeq") compareArguments afterCompare := by
  simp only [emptyGuard,emptyLeafCall,emptyFinish,updateGuard,updateBody,compareCall,compareArguments,leafArguments,
    afterCompare,afterKeys,afterLeaf,afterStride,afterLength,body,Guest.Software.guestFn_htab_set,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

end InitECandidate.Solver.Input.CurrentTable.Set

#print axioms InitECandidate.Solver.Input.CurrentTable.Set.guard_shapes
