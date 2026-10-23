import InitECandidate.Solver.Mpt.CollapseBranchProgram

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterValue : ProgHOL 64:=match afterScan with | .dec _ _ _ rest=>rest | _=>.skip
def emptyChoice : ProgHOL 64:=match afterValue with | .seq first _=>first | _=>.skip
def afterEmpty : ProgHOL 64:=match afterValue with | .seq _ rest=>rest | _=>.skip
def emptyBlock : ProgHOL 64:=match emptyChoice with | .ite _ yes _=>yes | _=>.skip
def emptyGuard : ProgHOL 64:=match emptyBlock with | .seq first _=>first | _=>.skip
def emptyLeaf : ProgHOL 64:=match emptyBlock with | .seq _ rest=>rest | _=>.skip
def singleChoice : ProgHOL 64:=match afterEmpty with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterEmpty with | .seq _ rest=>rest | _=>.skip
def childScope : ProgHOL 64:=match singleChoice with | .ite _ yes _=>yes | _=>.skip
def kindScope : ProgHOL 64:=match childScope with | .dec _ _ _ rest=>rest | _=>.skip
def afterKind : ProgHOL 64:=match kindScope with | .dec _ _ _ rest=>rest | _=>.skip
def hashGuard : ProgHOL 64:=match afterKind with | .seq first _=>first | _=>.skip
def nibbleScope : ProgHOL 64:=match afterKind with | .seq _ rest=>rest | _=>.skip
def afterNibble : ProgHOL 64:=match nibbleScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def nibbleStore : ProgHOL 64:=match afterNibble with | .seq first _=>first | _=>.skip
def afterStore : ProgHOL 64:=match afterNibble with | .seq _ rest=>rest | _=>.skip
def branchGuard : ProgHOL 64:=match afterStore with | .seq first _=>first | _=>.skip
def concatScope : ProgHOL 64:=match afterStore with | .seq _ rest=>rest | _=>.skip
def afterConcat : ProgHOL 64:=match concatScope with | .decCall _ _ _ _ rest=>rest | _=>.skip
def leafGuard : ProgHOL 64:=match afterConcat with | .seq first _=>first | _=>.skip
def extensionTail : ProgHOL 64:=match afterConcat with | .seq _ rest=>rest | _=>.skip
def field (name : String) (offset : BitVec 64) : ExpHOL 64:=.load .one (.op .add [localVar name,.const offset])
def singleTest : ExpHOL 64:=.op .and [.cmp .notEqual (.const 0#64) (.cmp .equal (localVar "count") (.const 1#64)),
  .cmp .notEqual (.const 0#64) (.cmp .equal (localVar "vl") (.const 0#64))]
def emptyArguments : List (ExpHOL 64):=[localVar "node",.const 0#64,field "node" 160#64,localVar "vl"]
def branchArguments : List (ExpHOL 64):=[localVar "nib",.const 1#64,localVar "child"]
def concatArguments : List (ExpHOL 64):=[localVar "nib",.const 1#64,field "child" 32#64,field "child" 40#64]
def joinedLength : ExpHOL 64:=.op .add [.const 1#64,field "child" 40#64]
def leafArguments : List (ExpHOL 64):=[localVar "cat",joinedLength,field "child" 48#64,field "child" 56#64]
def extensionArguments : List (ExpHOL 64):=[localVar "cat",joinedLength,field "child" 48#64]

theorem value_shapes : afterScan=.dec (ofString "vl") .one (field "node" 168#64) afterValue ∧
    afterValue=.seq emptyChoice afterEmpty ∧ emptyChoice=.ite (.cmp .equal (localVar "count") (.const 0#64)) emptyBlock .skip ∧
    emptyBlock=.seq emptyGuard emptyLeaf ∧
    emptyGuard=.ite (.cmp .equal (localVar "vl") (.const 0#64)) (.call (some (none,none)) (ofString "mpt_fail") [.const 12#64]) .skip ∧
    emptyLeaf=.call none (ofString "node_new_leaf") emptyArguments ∧ afterEmpty=.seq singleChoice footer ∧
    singleChoice=.ite singleTest childScope .skip ∧ footer=.return (localVar "node") := by
  simp only [afterScan,afterCounter,afterIndex,afterCount,body,afterValue,emptyChoice,afterEmpty,emptyBlock,emptyGuard,emptyLeaf,singleChoice,footer,
    childScope,singleTest,field,emptyArguments,Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

theorem child_shapes : childScope=.dec (ofString "child") .one (.load .one (childAddress (localVar "idx"))) kindScope ∧
    kindScope=.dec (ofString "ck") .one (field "child" 0#64) afterKind ∧ afterKind=.seq hashGuard nibbleScope ∧
    hashGuard=.ite (.cmp .equal (localVar "ck") (.const 0#64)) (.call (some (none,none)) (ofString "mpt_fail") [.const 2#64]) .skip ∧
    nibbleScope=.decCall (ofString "nib") .one (ofString "alloc") [.const 8#64] afterNibble ∧ afterNibble=.seq nibbleStore afterStore ∧
    nibbleStore=.storeByte (localVar "nib") (localVar "idx") := by
  simp only [childScope,kindScope,afterKind,hashGuard,nibbleScope,afterNibble,nibbleStore,afterStore,singleChoice,afterEmpty,afterValue,
    afterScan,afterCounter,afterIndex,afterCount,body,childAddress,field,Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,
    List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

theorem merge_shapes : afterStore=.seq branchGuard concatScope ∧
    branchGuard=.ite (.cmp .equal (localVar "ck") (.const 3#64)) (.call none (ofString "node_new_ext") branchArguments) .skip ∧
    concatScope=.decCall (ofString "cat") .one (ofString "nibbles_concat") concatArguments afterConcat ∧ afterConcat=.seq leafGuard extensionTail ∧
    leafGuard=.ite (.cmp .equal (localVar "ck") (.const 1#64)) (.call none (ofString "node_new_leaf") leafArguments) .skip ∧
    extensionTail=.call none (ofString "node_new_ext") extensionArguments := by
  simp only [afterStore,branchGuard,concatScope,afterConcat,leafGuard,extensionTail,branchArguments,concatArguments,leafArguments,extensionArguments,joinedLength,
    afterNibble,nibbleScope,afterKind,kindScope,childScope,singleChoice,afterEmpty,afterValue,afterScan,afterCounter,afterIndex,afterCount,body,
    field,Guest.guestFn__collapse_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar]
  simp

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.value_shapes
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.child_shapes
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.merge_shapes
