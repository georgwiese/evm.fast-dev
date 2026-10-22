import InitECandidate.Solver.Mpt.StateInitBlockCost

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix MutableTable
open Flapjack.Basis.Pure.MlString

/-- All outcomes of the unchanged workspace storage-table/block/journal
suffix, with no heap, mapping, scalar-global or future-return premise. -/
theorem after_root_store_cost (code) (installed : Input.OriginalCode.Installed code) :
    Input.ClockCost.Bound code afterRootStore 1758:=by
  rw [storage_shapes.1]
  have tail : Input.ClockCost.Bound code afterStorageTable 1662:=by
    rw [storage_shapes.2]
    have stored : Input.ClockCost.Bound code (store 32 "t") 0:=Input.ClockCost.store code _ _
    exact Input.ClockCost.sequence code _ _ 0 1662 stored (Block.body_cost code installed)
  intro source codeEq
  have sourceInstalled : Input.OriginalCode.Installed source.code:=by rewrite [codeEq]; exact installed
  have actual:=TableRuntime.scoped_cost source .word 64 (ofString "t") storageArguments afterStorageTable 1662 (by decide)
    sourceInstalled rfl (by rewrite [codeEq]; exact tail)
  have price : TableRuntime.costPrice 64=96:=by decide
  rewrite [price] at actual
  exact actual

theorem after_root_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterRoot 1758:=by
  rw [after_root_store_shape]
  have stored : Input.ClockCost.Bound code (store 24 "root") 0:=Input.ClockCost.store code _ _
  exact Input.ClockCost.sequence code _ _ 0 1758 stored (after_root_store_cost code installed)

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.after_root_store_cost
#print axioms InitECandidate.Solver.Mpt.StateInit.after_root_cost
