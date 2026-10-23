import InitECandidate.Solver.Mpt.DeleteExtensionProgram
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.Input.ClockCostCurrentGuard
import InitECandidate.Solver.Input.TailCallNoFallthrough

namespace InitECandidate.Solver.Mpt.DeleteExtension
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem scalar_tail_price (kind : NodeConstructor.Kind) (scalar : kind≠.branch) (code)
    (installed : Input.OriginalCode.Installed code) (arguments : List (ExpHOL 64)) :
    Input.ClockCost.Bound code (.call none (ofString (NodeConstructor.name kind)) arguments) 3 := by
  simpa only [Input.LocalEffects.callInfo,Option.map_none] using Input.ClockCost.call_body code none (ofString (NodeConstructor.name kind)) arguments
    (NodeConstructor.formals kind) (NodeConstructor.body kind) .one 2 (NodeConstructor.original_code kind code installed) (NodeConstructor.scalar_body_price kind scalar code installed)

/-- Original tail calls stop, so only one constructor is charged, even
on errors, allocation failures, exceptions or timeouts. -/
theorem constructor_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterLength 3 := by
  rw [merge_shapes.2.2.2.2.1,merge_shapes.2.2.2.2.2.1,merge_shapes.2.2.2.2.2.2]
  intro source same
  have extension : source.clock-(evaluateHOLFiniteState source (.call none (ofString "node_new_ext") extensionArguments)).2.clock≤3:=
    scalar_tail_price .extension (by decide) code installed extensionArguments source same
  have leaf : source.clock-(evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") leafArguments)).2.clock≤3:=
    scalar_tail_price .leaf (by decide) code installed leafArguments source same
  exact Input.ClockCost.stopping_guard_current source _ _ _ 3 3 (Input.NoFallthrough.tail_call _ _ source) extension leaf

theorem length_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code lengthScope 3 := by
  rw [merge_shapes.2.2.2.1]
  exact Input.ClockCost.declared code _ _ _ _ 3 (constructor_price code installed)

theorem branch_finish_quiet (code) : Input.QuietClock.Preserves code branchFinish := by
  rw [branchFinish]
  exact Input.QuietClock.sequence code _ _ (Input.QuietClock.store code _ _) (Input.QuietClock.returned code _)

end InitECandidate.Solver.Mpt.DeleteExtension

#print axioms InitECandidate.Solver.Mpt.DeleteExtension.scalar_tail_price
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.constructor_price
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.length_price
#print axioms InitECandidate.Solver.Mpt.DeleteExtension.branch_finish_quiet
