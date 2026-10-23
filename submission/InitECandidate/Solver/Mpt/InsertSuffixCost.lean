import InitECandidate.Solver.Mpt.InsertDispatchProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Mpt.SplitExtensionCost
import InitECandidate.Solver.Mpt.InsertEmptyCost
import InitECandidate.Solver.Input.ClockCostCall
import InitECandidate.Solver.Input.ClockCostScoped

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString

/-- All constructor outcomes, including lookup, shape and allocation failures. -/
theorem scalar_assigned_price (kind : NodeConstructor.Kind) (scalar : kind≠.branch) (code)
    (installed : Input.OriginalCode.Installed code) (name : MlS) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call (some (some (.local,name),none)) (ofString (NodeConstructor.name kind)) arguments) 3 := by
  simpa only [Input.LocalEffects.callInfo,Option.map_some] using Input.ClockCost.call_body code (some (some name)) (ofString (NodeConstructor.name kind)) arguments
    (NodeConstructor.formals kind) (NodeConstructor.body kind) .one 2 (NodeConstructor.original_code kind code installed) (NodeConstructor.scalar_body_price kind scalar code installed)

theorem extension_result_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code extensionSplitChoice 3 := by
  rw [extension_shapes.2.2.2.2.2.1,extension_shapes.2.2.2.2.2.2.1,extension_shapes.2.2.2.2.2.2.2]
  exact Input.ClockCost.conditional code _ _ _ 3 0
    (by simpa only [NodeConstructor.name] using scalar_assigned_price .extension (by decide) code installed (ofString "r") extensionArguments)
    (Input.ClockCost.assign code _ _)

theorem extension_split_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code extensionSplitScope 240 := by
  rw [extension_shapes.2.2.2.2.1]
  exact Input.ClockCost.scoped_body code (ofString "br") .one (ofString "_split_extension") splitArguments extensionSplitChoice SplitExtension.formals SplitExtension.body .one 236 3
    (SplitExtension.original_code code installed) (SplitExtension.body_price code installed) (extension_result_price code installed)

theorem extension_descend_quiet (code) : Input.QuietClock.Preserves code extensionDescend := by
  rw [extension_descend_shape]
  repeat first
    | apply Input.QuietClock.sequence
    | exact Input.QuietClock.assign code _ _

theorem extension_prefix_choice_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code extensionPrefixChoice 240 := by
  rw [extension_shapes.2.2.2.1]
  exact Input.ClockCost.conditional code _ _ _ 0 240
    (Input.ClockCost.of_quiet code _ (extension_descend_quiet code)) (extension_split_price code installed)

theorem branch_quiet (code) : Input.QuietClock.Preserves code branchChoice := by
  rw [branch_shapes.1,branch_shapes.2.1,branch_shapes.2.2.1,branch_shapes.2.2.2]
  repeat first
    | apply Input.QuietClock.conditional
    | apply Input.QuietClock.sequence
    | apply Input.QuietClock.declared
    | exact Input.QuietClock.assign code _ _
    | exact Input.QuietClock.store code _ _

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.scalar_assigned_price
#print axioms InitECandidate.Solver.Mpt.Insert.extension_result_price
#print axioms InitECandidate.Solver.Mpt.Insert.extension_split_price
#print axioms InitECandidate.Solver.Mpt.Insert.extension_descend_quiet
#print axioms InitECandidate.Solver.Mpt.Insert.extension_prefix_choice_price
#print axioms InitECandidate.Solver.Mpt.Insert.branch_quiet
