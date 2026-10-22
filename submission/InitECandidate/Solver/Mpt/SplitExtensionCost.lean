import InitECandidate.Solver.Mpt.TwoLeavesCost
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt.SplitExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64:=match Guest.guestFn__split_extension with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "node",.one),(ofString "rk",.one),(ofString "rl",.one),
  (ofString "vptr",.one),(ofString "vlen",.one),(ofString "pl",.one)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_split_extension")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 250 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.guestFn__split_extension) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.guestFn__split_extension,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
/-- The real split helper contains no unbounded traversal. Its literal
branch allocation, at most two scalar constructors, and collision failure
are priced at every outcome, without assuming valid stored path nibbles. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code body 236 := by
  have scalar (kind : NodeConstructor.Kind) (scalar : kind≠.branch) (name : MlS) (arguments : List (ExpHOL 64)) (address value : ExpHOL 64) :
      Input.ClockCost.Bound code (.decCall name .one (ofString (NodeConstructor.name kind)) arguments (.store address value)) 3:=
    Input.ClockCost.scoped_body code name .one _ arguments (.store address value)
      (NodeConstructor.formals kind) (NodeConstructor.body kind) .one 2 0
      (NodeConstructor.original_code kind code installed) (NodeConstructor.scalar_body_price kind scalar code installed)
      (Input.ClockCost.store code address value)
  simp only [body,Guest.guestFn__split_extension,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_none]
  apply Input.ClockCost.declared
  apply Input.ClockCost.declared
  apply Input.ClockCost.declared
  apply Input.ClockCost.scoped_body code _ _ _ _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one 228 7
    (NodeConstructor.original_code .branch code installed) (NodeConstructor.branch_uniform_price code installed)
  apply Input.ClockCost.declared
  apply Input.ClockCost.sequence code _ _ 0 7
  · exact Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.skip code)
  · apply Input.ClockCost.sequence code _ _ 3 4
    · exact Input.ClockCost.conditional code _ _ _ 3 0 (scalar .extension (by decide) _ _ _ _) (Input.ClockCost.skip code)
    · apply Input.ClockCost.declared
      apply Input.ClockCost.sequence code _ _ 4 0
      · apply Input.ClockCost.conditional code _ _ _ 0 4
        · exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.store code _ _)
        · apply Input.ClockCost.declared
          apply Input.ClockCost.sequence code _ _ 1 3
          · exact Input.ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed _) (Input.ClockCost.skip code)
          · exact scalar .leaf (by decide) _ _ _ _
      · exact Input.ClockCost.returned code _

end InitECandidate.Solver.Mpt.SplitExtension

#print axioms InitECandidate.Solver.Mpt.SplitExtension.original_code
#print axioms InitECandidate.Solver.Mpt.SplitExtension.body_price
