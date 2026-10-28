import InitECandidate.Solver.Input.CurrentTable.NewCost
import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Input.CurrentTable.New
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterTable : ProgHOL 64 := match body with | .decCall _ _ _ _ rest=>rest | _=>.skip
def afterStride : ProgHOL 64 := match afterTable with | .dec _ _ _ rest=>rest | _=>.skip
def afterNcap : ProgHOL 64 := match afterStride with | .dec _ _ _ rest=>rest | _=>.skip
def fields : ProgHOL 64 := match afterNcap with | .seq _ rest=>rest | _=>.skip
def strideExpression : ExpHOL 64 := .op .and [.op .add [localVar "key_len",.const 7#64],.op .sub [.const 0#64,.const 8#64]]
def capacityGuard : ProgHOL 64 := .ite (.cmp .lower (localVar "ncap") (.const 2#64)) (.assign .local (ofString "ncap") (.const 2#64)) .skip

set_option maxRecDepth 100000 in
theorem shapes :
    body=.decCall (ofString "t") .one (ofString "alloc") [.const 88#64] afterTable ∧
    afterTable=.dec (ofString "stride") .one strideExpression afterStride ∧
    afterStride=.dec (ofString "ncap") .one (localVar "cap") afterNcap ∧
    afterNcap=.seq capacityGuard fields := by
  simp only [body,afterTable,afterStride,afterNcap,fields,strideExpression,capacityGuard,
    Guest.Software.guestFn_htab_new,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,localVar]
  trivial

end InitECandidate.Solver.Input.CurrentTable.New

#print axioms InitECandidate.Solver.Input.CurrentTable.New.shapes
