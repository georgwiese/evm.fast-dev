import InitECandidate.Solver.Mpt.InsertExtensionCost
import InitECandidate.Solver.Mpt.InsertionHelperEnvironment
import InitECandidate.Solver.Mpt.InsertScalarInputs
import InitECandidate.Solver.Input.ClockCostAssignedCurrent
import InitECandidate.Solver.Input.ClockCostCurrentConditional

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real assigned leaf helper is priced at every outcome using only
its genuine remaining-key scalar operands and installed original code. -/
theorem leaf_call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source insertLeafCall).2.clock≤563 := by
  have subtraction : (length-level).toNat=length.toNat-level.toNat:=BitVec.toNat_sub_of_le (by rwa [BitVec.le_def])
  have small : (length-level).toNat≤64:=by rw [subtraction]; omega
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) insertLeafArguments=
      some (InsertLeaf.callValues node (key+level) (length-level) pointer size):=by
    simp [insertLeafArguments,queryPointer,queryLength,InsertLeaf.callValues,evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,
      inputs.nodeCell,inputs.keyCell,inputs.levelCell,inputs.lengthCell,inputs.pointerCell,inputs.sizeCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  obtain ⟨callee,called,nodeCell,rkCell,rlCell,pointerCell,sizeCell⟩:=InsertLeaf.environment source node (key+level) (length-level) pointer size (InsertLeaf.original_code source.code installed)
  have price:=InsertLeaf.body_cost (callEntryStateHOLFinite source callee) (key+level) (length-level) small installed rkCell rlCell
  have priced : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) InsertLeaf.body).2.clock≤562:=price.trans (by omega)
  rw [dispatch_shapes.2.2.2.2.2.2.1]
  exact Input.ClockCost.assigned_current source (some (.local,ofString "r")) (ofString "_insert_into_leaf") insertLeafArguments _ InsertLeaf.body callee .one 562 args called priced

theorem extension_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source extensionChoice).2.clock≤306 := by
  rw [dispatch_shapes.2.2.2.2.2.2.2]
  exact Input.ClockCost.conditional_current source _ _ _ 306 0
    (extension_scope_cost source key level length bounded before installed inputs.keyCell inputs.levelCell inputs.lengthCell)
    ((Input.ClockCost.of_quiet source.code branchChoice (branch_quiet source.code)) source rfl)

/-- All original node-kind outcomes, including failed field reads, helper
calls, collisions, shape checks and resource failures, within563 ticks. -/
theorem kind_choice_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kindChoice).2.clock≤563 := by
  rw [dispatch_shapes.2.2.2.2.2.1]
  exact Input.ClockCost.conditional_current source _ _ _ 563 306
    (leaf_call_cost source node key level length pointer size inputs bounded before installed)
    (extension_choice_cost source node key level length pointer size inputs bounded before installed)

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.leaf_call_cost
#print axioms InitECandidate.Solver.Mpt.Insert.extension_choice_cost
#print axioms InitECandidate.Solver.Mpt.Insert.kind_choice_cost
