import InitECandidate.Solver.Input.SharedStoreLocal
import InitECandidate.Solver.Input.CounterFlow

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix.QueryBranch

/-- Actual ordinary byte stores retain every current caller binding on
continuation and cannot escape as return, break or continue. -/
theorem byte_store_local {F : Type} (key : MlS) (address value : ExpHOL 64) (source : PanSemStateFiniteExact 64 F) :
    LocalSummary key (.storeByte address value) source :=
  (LocalPrefix.storeByte address value).summary_full source

/-- A normal ordinary byte store advances no current caller counter. -/
theorem CounterFlow.byte_store (key : MlS) (address value : ExpHOL 64) : Advances key 0 (.storeByte address value) := by
  intro source post word cell run
  have summary := byte_store_local key address value source
  unfold LocalSummary at summary
  rw [run] at summary
  simpa only [BitVec.add_zero] using (summary.1 rfl).trans cell


end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.byte_store_local
#print axioms InitECandidate.Solver.Input.CounterFlow.byte_store
