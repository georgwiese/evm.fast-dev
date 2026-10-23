import InitECandidate.Solver.Mpt.LeafInsertDispatch

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchArguments : List (ExpHOL 64):=
  [.op .add [localVar "ek",localVar "pl"],.op .sub [localVar "el",localVar "pl"],
    .load .one (addConst (localVar "node") 48#64),.load .one (addConst (localVar "node") 56#64),
    .op .add [localVar "rk",localVar "pl"],.op .sub [localVar "rl",localVar "pl"],localVar "vptr",localVar "vlen"]
def afterBranch : ProgHOL 64:=match afterPrefix with | .decCall _ _ _ _ rest=>rest | _=>.skip
def prefixPositive : ExpHOL 64:=.cmp .lower (.const 0#64) (localVar "pl")
def extensionArguments : List (ExpHOL 64):=[localVar "ek",localVar "pl",localVar "br"]
def extensionCall : ProgHOL 64:=.call none (ofString "node_new_ext") extensionArguments
def branchFooter : ProgHOL 64:=.return (localVar "br")

set_option maxRecDepth 100000 in
theorem split_shapes : afterPrefix=.decCall (ofString "br") .one (ofString "_create_branch_from_two_leaves") branchArguments afterBranch ∧
    afterBranch=.seq (.ite prefixPositive extensionCall .skip) branchFooter := by
  simp only [afterBranch,afterPrefix,splitScope,afterLength,afterKey,body,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,branchArguments,prefixPositive,extensionCall,extensionArguments,branchFooter,localVar,addConst]
  simp

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.split_shapes
