import InitECandidate.Solver.Mpt.TwoLeavesCost
import InitECandidate.Solver.Mpt.BranchValueStores

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterBranch : ProgHOL 64:=match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def firstChoice : ProgHOL 64:=match afterBranch with | .seq first _=>first | _=>.skip
def afterFirst : ProgHOL 64:=match afterBranch with | .seq _ rest=>rest | _=>.skip
def secondChoice : ProgHOL 64:=match afterFirst with | .seq first _=>first | _=>.skip
def footer : ProgHOL 64:=match afterFirst with | .seq _ rest=>rest | _=>.skip
def choice (second : Bool) : ProgHOL 64:=if second then secondChoice else firstChoice
def label (second : Bool) (first last : String) : String:=if second then last else first
def leafScope (second : Bool) : ProgHOL 64:=match choice second with | .ite _ _ no=>no | _=>.skip
def leafArguments (second : Bool) : List (ExpHOL 64):=
  [addConst (localVar (label second "k1" "k2")) 1#64,
    .op .sub [localVar (label second "l1" "l2"),.const 1#64],
    localVar (label second "v1" "v2"),localVar (label second "vl1" "vl2")]
def leafStore (second : Bool) : ProgHOL 64:=match leafScope second with | .decCall _ _ _ _ rest=>rest | _=>.skip
def childAddress (second : Bool) : ExpHOL 64:=
  .op .add [localVar "br",.const 32#64,.panop .mul [.loadByte (localVar (label second "k1" "k2")),.const 8#64]]

set_option maxRecDepth 100000 in
theorem program_shapes : body=.decCall (ofString "br") .one (ofString "node_new_branch") [] afterBranch ∧
    afterBranch=.seq firstChoice afterFirst ∧ afterFirst=.seq secondChoice footer ∧ footer=.return (localVar "br") := by
  simp only [body,afterBranch,firstChoice,afterFirst,secondChoice,footer,Guest.guestFn__create_branch_from_two_leaves,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  simp

set_option maxRecDepth 100000 in
theorem side_shapes (second : Bool) :
    choice second=.ite (.cmp .equal (localVar (label second "l1" "l2")) (.const 0#64))
      (BranchValueUpdate.stores "br" (label second "v1" "v2") (label second "vl1" "vl2")) (leafScope second) ∧
    leafScope second=.decCall (ofString (label second "lf1" "lf2")) .one (ofString "node_new_leaf") (leafArguments second) (leafStore second) ∧
    leafStore second=.store (childAddress second) (localVar (label second "lf1" "lf2")) := by
  cases second <;>
    simp only [choice,label,leafScope,leafArguments,leafStore,childAddress,firstChoice,secondChoice,afterFirst,afterBranch,body,
      Guest.guestFn__create_branch_from_two_leaves,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
      BranchValueUpdate.stores,localVar,addConst,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.program_shapes
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.side_shapes
