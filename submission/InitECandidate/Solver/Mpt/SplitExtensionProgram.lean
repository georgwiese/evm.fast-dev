import InitECandidate.Solver.Mpt.SplitExtensionCost
import InitECandidate.Solver.Mpt.BranchValueStores

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fieldExpression (offset : BitVec 64) : ExpHOL 64:=.load .one (addConst (localVar "node") offset)
def afterSegment : ProgHOL 64:=match body with | .dec _ _ _ rest=>rest | _=>.skip
def afterLength : ProgHOL 64:=match afterSegment with | .dec _ _ _ rest=>rest | _=>.skip
def branchScope : ProgHOL 64:=match afterLength with | .dec _ _ _ rest=>rest | _=>.skip
def afterBranch : ProgHOL 64:=match branchScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def oldRemainder : ExpHOL 64:=.op .sub [localVar "sl",localVar "pl"]
def oldChoices : ProgHOL 64:=match afterBranch with | .dec _ _ _ rest=>rest | _=>.skip
def oldSingleChoice : ProgHOL 64:=match oldChoices with | .seq first _=>first | _=>.skip
def afterSingle : ProgHOL 64:=match oldChoices with | .seq _ rest=>rest | _=>.skip
def oldLongChoice : ProgHOL 64:=match afterSingle with | .seq first _=>first | _=>.skip
def newRemainderScope : ProgHOL 64:=match afterSingle with | .seq _ rest=>rest | _=>.skip
def newRemainder : ExpHOL 64:=.op .sub [localVar "rl",localVar "pl"]
def afterNewRemainder : ProgHOL 64:=match newRemainderScope with | .dec _ _ _ rest=>rest | _=>.skip
def newChoice : ProgHOL 64:=match afterNewRemainder with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterNewRemainder with | .seq _ rest=>rest | _=>.skip
def oldAtPrefix : ExpHOL 64:=.op .add [localVar "seg",localVar "pl"]
def oldChildAddress : ExpHOL 64:=.op .add [localVar "br",.const 32#64,.panop .mul [.loadByte oldAtPrefix,.const 8#64]]
def oldChildStore : ProgHOL 64:=.store oldChildAddress (localVar "child")
def oldExtensionScope : ProgHOL 64:=match oldLongChoice with | .ite _ yes _=>yes | _=>.skip
def oldExtensionArguments : List (ExpHOL 64):=[.op .add [localVar "seg",localVar "pl",.const 1#64],
  .op .sub [localVar "sal",.const 1#64],localVar "child"]
def oldExtensionStore : ProgHOL 64:=.store oldChildAddress (localVar "ex")
def newIndex : ExpHOL 64:=.loadByte (.op .add [localVar "rk",localVar "pl"])
def newNonzeroScope : ProgHOL 64:=match newChoice with | .ite _ _ no=>no | _=>.skip
def afterIndex : ProgHOL 64:=match newNonzeroScope with | .dec _ _ _ rest=>rest | _=>.skip
def collisionGuard : ProgHOL 64:=match afterIndex with | .seq first _=>first | _=>.skip
def newLeafScope : ProgHOL 64:=match afterIndex with | .seq _ rest=>rest | _=>.skip
def newChildAddress : ExpHOL 64:=.op .add [localVar "br",.const 32#64,.panop .mul [localVar "idx",.const 8#64]]
def collisionTest : ExpHOL 64:=.cmp .notEqual (.load .one newChildAddress) (.const 0#64)
def newLeafArguments : List (ExpHOL 64):=[.op .add [localVar "rk",localVar "pl",.const 1#64],
  .op .sub [localVar "kal",.const 1#64],localVar "vptr",localVar "vlen"]
def newLeafStore : ProgHOL 64:=.store newChildAddress (localVar "lf")

set_option maxRecDepth 100000 in
theorem entry_shapes : body=.dec (ofString "seg") .one (fieldExpression 32#64) afterSegment ∧
    afterSegment=.dec (ofString "sl") .one (fieldExpression 40#64) afterLength ∧
    afterLength=.dec (ofString "child") .one (fieldExpression 48#64) branchScope ∧
    branchScope=.decCall (ofString "br") .one (ofString "node_new_branch") [] afterBranch ∧
    afterBranch=.dec (ofString "sal") .one oldRemainder oldChoices := by
  simp only [fieldExpression,body,afterSegment,afterLength,branchScope,afterBranch,oldChoices,oldRemainder,
    Guest.guestFn__split_extension,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar,addConst]
  simp

set_option maxRecDepth 100000 in
theorem old_shapes : oldChoices=.seq oldSingleChoice afterSingle ∧ afterSingle=.seq oldLongChoice newRemainderScope ∧
    oldSingleChoice=.ite (.cmp .equal (localVar "sal") (.const 1#64)) oldChildStore .skip ∧
    oldLongChoice=.ite (.cmp .lower (.const 1#64) (localVar "sal")) oldExtensionScope .skip ∧
    oldExtensionScope=.decCall (ofString "ex") .one (ofString "node_new_ext") oldExtensionArguments oldExtensionStore := by
  simp only [oldChoices,oldSingleChoice,afterSingle,oldLongChoice,newRemainderScope,oldChildStore,oldChildAddress,oldAtPrefix,oldExtensionScope,
    oldExtensionArguments,oldExtensionStore,afterBranch,branchScope,afterLength,afterSegment,body,Guest.guestFn__split_extension,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  simp

set_option maxRecDepth 100000 in
theorem new_shapes : newRemainderScope=.dec (ofString "kal") .one newRemainder afterNewRemainder ∧ afterNewRemainder=.seq newChoice footer ∧
    newChoice=.ite (.cmp .equal (localVar "kal") (.const 0#64)) (BranchValueUpdate.stores "br" "vptr" "vlen") newNonzeroScope ∧
    newNonzeroScope=.dec (ofString "idx") .one newIndex afterIndex ∧ afterIndex=.seq collisionGuard newLeafScope ∧
    collisionGuard=.ite collisionTest (.call (some (none,none)) (ofString "mpt_fail") [.const 11#64]) .skip ∧
    newLeafScope=.decCall (ofString "lf") .one (ofString "node_new_leaf") newLeafArguments newLeafStore ∧ footer=.return (localVar "br") := by
  simp only [newRemainderScope,newRemainder,afterNewRemainder,newChoice,footer,newNonzeroScope,newIndex,afterIndex,collisionGuard,newLeafScope,
    collisionTest,newChildAddress,newLeafArguments,newLeafStore,BranchValueUpdate.stores,afterSingle,oldChoices,afterBranch,branchScope,afterLength,afterSegment,body,
    Guest.guestFn__split_extension,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar,addConst]
  simp

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.entry_shapes
#print axioms InitECandidate.Solver.Mpt.SplitExtension.old_shapes
#print axioms InitECandidate.Solver.Mpt.SplitExtension.new_shapes
