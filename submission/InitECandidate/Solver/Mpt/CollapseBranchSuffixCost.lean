import InitECandidate.Solver.Mpt.CollapseBranchSuffixProgram
import InitECandidate.Solver.Mpt.DeleteExtensionSuffixCost
import InitECandidate.Solver.Mpt.Fail

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Only the selected stopping constructor is charged, including failed
allocation, lookup/shape failures and timeouts. -/
theorem constructor_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterConcat 3 := by
  rw [merge_shapes.2.2.2.1,merge_shapes.2.2.2.2.1,merge_shapes.2.2.2.2.2]
  intro source same
  have leaf : source.clock-(evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") leafArguments)).2.clock≤3:=
    DeleteExtension.scalar_tail_price .leaf (by decide) code installed leafArguments source same
  have extension : source.clock-(evaluateHOLFiniteState source (.call none (ofString "node_new_ext") extensionArguments)).2.clock≤3:=
    DeleteExtension.scalar_tail_price .extension (by decide) code installed extensionArguments source same
  exact Input.ClockCost.stopping_guard_current source _ _ _ 3 3 (Input.NoFallthrough.tail_call _ _ source) leaf extension

theorem empty_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code emptyBlock 3 := by
  rw [value_shapes.2.2.2.1,value_shapes.2.2.2.2.1,value_shapes.2.2.2.2.2.1]
  intro source same
  have currentInstalled : Input.OriginalCode.Installed source.code:=by rw [same]; exact installed
  have stops : (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "mpt_fail") [.const 12#64])).1≠none:=by
    intro normal
    exact Fail.call_not_normal source _ currentInstalled _ (Prod.ext normal rfl)
  have failure:=Fail.call_price code installed [.const 12#64] source same
  have leaf : source.clock-(evaluateHOLFiniteState source (.call none (ofString "node_new_leaf") emptyArguments)).2.clock≤3:=
    DeleteExtension.scalar_tail_price .leaf (by decide) code installed emptyArguments source same
  exact Input.ClockCost.stopping_guard_current source _ _ _ 1 3 stops failure leaf

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.constructor_price
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.empty_price
