import InitECandidate.Solver.WitnessRadix.TableFinish

namespace InitECandidate.Solver.WitnessRadix.TableNew
open Flapjack PanSemStateFiniteExact
open QueryBranch

theorem initial_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (capLocal : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "cap") =
      some (.val (.word (BitVec.ofNat 64 plan.capacity)))) :
    Locals (initialState source plan) (BitVec.ofNat 64 plan.table) plan.capacity := by
  let allocated := PersistentAlloc.nextState source "t" plan.table (plan.table + 72)
  refine ⟨?_, ?_, bind_lookup_same _ _ _⟩
  · change (bind allocated "stride" 32#64).locals.lookup (Flapjack.Basis.Pure.MlString.ofString "t") = _
    rw [bind_lookup_other allocated "stride" "t" _ (by decide)]
    exact bind_lookup_same _ _ _
  · change (bind allocated "stride" 32#64).locals.lookup (Flapjack.Basis.Pure.MlString.ofString "cap") = _
    rw [bind_lookup_other allocated "stride" "cap" _ (by decide)]
    unfold allocated PersistentAlloc.nextState
    rw [bind_lookup_other _ "t" "cap" _ (by decide)]
    exact capLocal

theorem preclear_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (locals : Locals source (BitVec.ofNat 64 plan.table) plan.capacity) :
    Locals (preClearState source plan) (BitVec.ofNat 64 plan.table) plan.capacity := by
  have keys := locals_allocated source _ _ locals "keys" (plan.table + 72)
    (plan.table + 72 + 32 * plan.capacity) (by decide) (by decide) (by decide)
  have storedKeys : Locals (keysStored source plan) _ _ := ⟨keys.tableLocal, keys.capLocal, keys.strideLocal⟩
  have vals := locals_allocated (keysStored source plan) _ _ storedKeys "vals"
    (plan.table + 72 + 32 * plan.capacity) (plan.table + 72 + 40 * plan.capacity) (by decide) (by decide) (by decide)
  have storedVals : Locals (valsStored source plan) _ _ := ⟨vals.tableLocal, vals.capLocal, vals.strideLocal⟩
  exact locals_allocated (valsStored source plan) _ _ storedVals "used" _ _ (by decide) (by decide) (by decide)

theorem finish_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (plan : AllocatedLayout.Plan)
    (locals : Locals source (BitVec.ofNat 64 plan.table) plan.capacity) :
    Locals (finishState source plan) (BitVec.ofNat 64 plan.table) plan.capacity := by
  have storedUsed : Locals (usedStored source plan) _ _ := ⟨locals.tableLocal, locals.capLocal, locals.strideLocal⟩
  have order := locals_allocated (usedStored source plan) _ _ storedUsed "order"
    (plan.table + 72 + 41 * plan.capacity + plan.padding) (plan.table + 72 + 49 * plan.capacity + plan.padding)
    (by decide) (by decide) (by decide)
  have storedOrder : Locals (orderStored source plan) _ _ := ⟨order.tableLocal, order.capLocal, order.strideLocal⟩
  have backup := locals_allocated (orderStored source plan) _ _ storedOrder "order_pos"
    (plan.table + 72 + 49 * plan.capacity + plan.padding) (plan.table + 72 + 57 * plan.capacity + plan.padding)
    (by decide) (by decide) (by decide)
  exact ⟨backup.tableLocal, backup.capLocal, backup.strideLocal⟩

end InitECandidate.Solver.WitnessRadix.TableNew

#print axioms InitECandidate.Solver.WitnessRadix.TableNew.initial_locals
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.preclear_locals
#print axioms InitECandidate.Solver.WitnessRadix.TableNew.finish_locals
