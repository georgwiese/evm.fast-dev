import InitECandidate.Solver.Mpt.NodeConstructorFields
import InitECandidate.Solver.Input.QuietClock

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def branchArguments : List (ExpHOL 64):=[QueryBranch.localVar "nd",.const 176#64]
def branchZero : ProgHOL 64:=.call (some (none,none)) (ofString "memzero") branchArguments
def branchFields : List FieldStores.Field:=[⟨0,.literal 3#64⟩]
def branchFooter : ProgHOL 64:=FieldStores.program "nd" "" branchFields (.return (QueryBranch.localVar "nd"))

set_option maxRecDepth 100000 in
theorem branch_tail_shape : tail .branch=.seq branchZero branchFooter := by
  simp only [tail,body,original,branchZero,branchArguments,branchFooter,branchFields,FieldStores.program,FieldStores.address,
    FieldStores.Value.expression,QueryBranch.addConst,QueryBranch.localVar,Guest.Software.guestFn_node_new_branch,Guest.guestFn_node_new_branch,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]

theorem branch_footer_quiet (code) : Input.QuietClock.Preserves code branchFooter := by
  exact Input.QuietClock.sequence code _ _ (Input.QuietClock.store code _ _) (Input.QuietClock.returned code _)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_tail_shape
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_footer_quiet
