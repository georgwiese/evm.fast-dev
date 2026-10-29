import InitECandidate.Solver.Mpt.NodeBranchAnyCost

namespace InitECandidate.Solver.Mpt.TwoLeaves
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def body : ProgHOL 64:=match Guest.guestFn__create_branch_from_two_leaves with | .function fn=>progToHOL fn.body | _=>.skip
def formals : List (MlS×ShapeHOL):=[(ofString "k1",.one),(ofString "l1",.one),(ofString "v1",.one),(ofString "vl1",.one),
  (ofString "k2",.one),(ofString "l2",.one),(ofString "v2",.one),(ofString "vl2",.one)]

set_option maxRecDepth 100000 in
theorem original_code (code) (installed : Input.OriginalCode.Installed code) :
    code.lookup (ofString "_create_branch_from_two_leaves")=some (formals,body,.one) := by
  have checked:=Input.OriginalCode.indexed code installed 246 (GasBudget.OriginalCodeEnvironment.originalEntry Guest.Software.guestFn__create_branch_from_two_leaves) (by rfl)
  simpa only [GasBudget.OriginalCodeEnvironment.originalEntry,declToHOL,funDeclToHOL,formals,body,Guest.Software.guestFn__create_branch_from_two_leaves,Guest.guestFn__create_branch_from_two_leaves,
    shapeToHOL,paramToHOL,List.map_cons,List.map_nil] using checked

set_option maxRecDepth 100000 in
/-- All outcomes of the unchanged two-leaf branch helper. Byte reads,
allocation guards and stores may fail; no nibble-range or room premise is
needed for this cost bound. Graph preservation is a separate obligation. -/
theorem body_price (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code body 235 := by
  have leaf (name : MlS) (arguments : List (ExpHOL 64)) (address value : ExpHOL 64) :
      Input.ClockCost.Bound code (.decCall name .one (ofString "node_new_leaf") arguments (.store address value)) 3:=
    Input.ClockCost.scoped_body code name .one (ofString "node_new_leaf") arguments (.store address value)
      (NodeConstructor.formals .leaf) (NodeConstructor.body .leaf) .one 2 0
      (NodeConstructor.original_code .leaf code installed) (NodeConstructor.scalar_body_price .leaf (by decide) code installed)
      (Input.ClockCost.store code address value)
  simp only [body,Guest.guestFn__create_branch_from_two_leaves,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  apply Input.ClockCost.scoped_body code _ _ _ _ _ (NodeConstructor.formals .branch) (NodeConstructor.body .branch) .one 228 6
    (NodeConstructor.original_code .branch code installed) (NodeConstructor.branch_uniform_price code installed)
  apply Input.ClockCost.sequence code _ _ 3 3
  · apply Input.ClockCost.conditional code _ _ _ 0 3
    · exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.store code _ _)
    · exact leaf _ _ _ _
  · apply Input.ClockCost.sequence code _ _ 3 0
    · apply Input.ClockCost.conditional code _ _ _ 0 3
      · exact Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) (Input.ClockCost.store code _ _)
      · exact leaf _ _ _ _
    · exact Input.ClockCost.returned code _

end InitECandidate.Solver.Mpt.TwoLeaves

#print axioms InitECandidate.Solver.Mpt.TwoLeaves.original_code
#print axioms InitECandidate.Solver.Mpt.TwoLeaves.body_price
