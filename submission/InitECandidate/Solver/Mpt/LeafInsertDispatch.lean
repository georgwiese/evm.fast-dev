import InitECandidate.Solver.Mpt.LeafUpdateProgram
import InitECandidate.Solver.Mpt.TwoLeavesCost
import InitECandidate.Solver.Input.LocalFlow

namespace InitECandidate.Solver.Mpt.InsertLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def keyExpression : ExpHOL 64:=.load .one (addConst (localVar "node") 32#64)
def lengthExpression : ExpHOL 64:=.load .one (addConst (localVar "node") 40#64)
def lengthTest : ExpHOL 64:=.cmp .equal (localVar "el") (localVar "rl")
def compareArguments : List (ExpHOL 64):=[localVar "ek",localVar "rk",localVar "el"]
def splitScope : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip
def prefixArguments : List (ExpHOL 64):=[localVar "ek",localVar "el",localVar "rk",localVar "rl"]
def afterPrefix : ProgHOL 64:=match splitScope with | .decCall _ _ _ _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem dispatch_shapes : body=.dec (ofString "ek") .one keyExpression afterKey ∧
    afterKey=.dec (ofString "el") .one lengthExpression afterLength ∧
    afterLength=.seq lengthChoice splitScope ∧ lengthChoice=.ite lengthTest compareScope .skip ∧
    compareScope=.decCall (ofString "eq") .one (ofString "memeq") compareArguments compareGuard ∧
    splitScope=.decCall (ofString "pl") .one (ofString "common_prefix_length") prefixArguments afterPrefix := by
  simp only [keyExpression,lengthExpression,lengthTest,compareArguments,splitScope,prefixArguments,afterPrefix,
    body,afterKey,afterLength,lengthChoice,compareScope,compareGuard,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none,localVar,addConst]
  simp

set_option maxRecDepth 100000 in
theorem compare_guard_quiet (code) : Input.QuietClock.Preserves code compareGuard := by
  simp only [compareGuard,compareScope,lengthChoice,afterLength,afterKey,body,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  repeat first
    | apply Input.QuietClock.conditional
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.store code _ _
    | exact Input.QuietClock.returned code _
    | exact Input.QuietClock.skip code

set_option maxRecDepth 100000 in
/-- A matching replacement may return early. If comparison instead
continues to the split, each saved caller operand is still the real one. -/
theorem length_choice_flow (key : MlS) (different : key≠ofString "eq") : Input.LocalFlow key lengthChoice := by
  rw [dispatch_shapes.2.2.2.1,dispatch_shapes.2.2.2.2.1]
  apply Input.LocalFlow.ite
  · apply Input.LocalFlow.decCall _ _ _ _ different
    simp only [compareGuard,compareScope,lengthChoice,afterLength,afterKey,body,Guest.guestFn__insert_into_leaf,
      progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
    repeat first
      | apply Input.LocalFlow.ite
      | apply Input.LocalFlow.seq
      | exact Input.LocalFlow.returned _
      | exact Input.LocalFlow.base (.store _ _)
      | exact Input.LocalFlow.base .skip
  · exact Input.LocalFlow.base .skip

set_option maxRecDepth 100000 in
theorem after_prefix_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code afterPrefix 239 := by
  simp only [afterPrefix,splitScope,afterLength,afterKey,body,Guest.guestFn__insert_into_leaf,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  apply Input.ClockCost.scoped_body code _ _ _ _ _ TwoLeaves.formals TwoLeaves.body .one 235 3
    (TwoLeaves.original_code code installed) (TwoLeaves.body_price code installed)
  apply Input.ClockCost.sequence code _ _ 3 0
  · apply Input.ClockCost.conditional code _ _ _ 3 0
    · exact Input.ClockCost.call_body code none _ _ (NodeConstructor.formals .extension) (NodeConstructor.body .extension) .one 2
        (NodeConstructor.original_code .extension code installed) (NodeConstructor.scalar_body_price .extension (by decide) code installed)
    · exact Input.ClockCost.skip code
  · exact Input.ClockCost.returned code _

end InitECandidate.Solver.Mpt.InsertLeaf

#print axioms InitECandidate.Solver.Mpt.InsertLeaf.dispatch_shapes
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.compare_guard_quiet
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.length_choice_flow
#print axioms InitECandidate.Solver.Mpt.InsertLeaf.after_prefix_price
