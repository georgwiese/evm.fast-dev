import InitECandidate.Solver.Mpt.InsertKindCost
import InitECandidate.Solver.Mpt.NodeInvalidate
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem invalidate_prefix_safe (name : MlS) : Input.LocalPrefix name invalidateCall := by
  rw [dispatch_shapes.2.2.2.2.1]
  exact .call none _ _ (by intro key impossible; cases impossible)

theorem hash_prefix_safe (name : MlS) : Input.LocalPrefix name hashGuard := by
  rw [dispatch_shapes.2.2.2.1]
  exact .ite _ (.call none _ _ (by intro key impossible; cases impossible)) .skip

theorem hash_guard_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code hashGuard 1 := by
  rw [dispatch_shapes.2.2.2.1]
  exact Input.ClockCost.conditional code _ _ _ 1 0 (Fail.call_price code installed _) (Input.ClockCost.skip code)

theorem after_hash_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterHash).2.clock≤564 := by
  have front : source.clock-(evaluateHOLFiniteState source invalidateCall).2.clock≤1:=by
    rw [dispatch_shapes.2.2.2.2.1]
    exact (Input.ClockCost.call_body source.code (some none) (ofString "node_invalidate") [localVar "node"] NodeInvalidate.formals NodeInvalidate.body .one 0
      (NodeInvalidate.original_code source.code installed) (Input.ClockCost.of_quiet source.code _ (NodeInvalidate.quiet source.code))) source rfl
  rw [dispatch_shapes.2.2.1]
  apply Input.ClockCost.sequence_reached_current source invalidateCall kindChoice 1 563 front
  intro middle normal
  have current:=inputs.after_prefix source middle node key level length pointer size invalidateCall invalidate_prefix_safe normal
  have codeEq:=(Input.evaluation_fields source middle invalidateCall none normal).2.2.2
  exact kind_choice_cost middle node key level length pointer size current bounded before (by rw [codeEq]; exact installed)

theorem after_kind_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source afterKind).2.clock≤565 := by
  rw [dispatch_shapes.2.1]
  apply Input.ClockCost.sequence_reached_current source hashGuard afterHash 1 564 ((hash_guard_price source.code installed) source rfl)
  intro middle normal
  have current:=inputs.after_prefix source middle node key level length pointer size hashGuard hash_prefix_safe normal
  have codeEq:=(Input.evaluation_fields source middle hashGuard none normal).2.2.2
  exact after_hash_cost middle node key level length pointer size current bounded before (by rw [codeEq]; exact installed)

/-- All original nonempty-node outcomes, including an unmapped or malformed
tag load, actual failing hash guard, invalidation and any later helper failure. -/
theorem nonempty_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source nonemptyChoice).2.clock≤565 := by
  rw [dispatch_shapes.1]
  apply Input.ClockCost.declared_reached_current
  intro loaded _read _checked
  let current:=setVarHOLFinite (ofString "k") loaded source
  have currentInputs:=inputs.after_update source current node key level length pointer size (ofString "k") loaded
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) rfl
  exact after_kind_cost current node key level length pointer size currentInputs bounded before installed

/-- Every actual original node-choice outcome within565 source clocks.
Only typed scalar operands and their bounded current query level are used. -/
theorem node_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source nodeChoice).2.clock≤565 := by
  have empty : source.clock-(evaluateHOLFiniteState source leafCall).2.clock≤3:=by
    rw [leafCall]
    simpa only [NodeConstructor.name] using (scalar_assigned_price .leaf (by decide) source.code installed (ofString "r") leafArguments) source rfl
  rw [node_choice_shape]
  exact Input.ClockCost.conditional_current source _ _ _ 3 565 empty
    (nonempty_choice_cost source node key level length pointer size inputs bounded before installed)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.invalidate_prefix_safe
#print axioms InitECandidate.Solver.Mpt.Insert.hash_prefix_safe
#print axioms InitECandidate.Solver.Mpt.Insert.hash_guard_price
#print axioms InitECandidate.Solver.Mpt.Insert.after_hash_cost
#print axioms InitECandidate.Solver.Mpt.Insert.after_kind_cost
#print axioms InitECandidate.Solver.Mpt.Insert.nonempty_choice_cost
#print axioms InitECandidate.Solver.Mpt.Insert.node_choice_cost
