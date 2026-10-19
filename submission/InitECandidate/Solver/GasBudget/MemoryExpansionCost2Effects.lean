import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Program
import InitECandidate.Solver.GasBudget.MemoryCostNoException

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem safe_guard (code) (name : String) : Input.NoException.Safe code (maxGuard name) :=
  Input.NoException.conditional code _ _ _ (Input.NoException.returned code _) (Input.NoException.skip code)

theorem guard_price (code) (name : String) : Input.ClockCost.Bound code (maxGuard name) 0 :=
  Input.ClockCost.conditional code _ _ _ 0 0 (Input.ClockCost.returned code _) (Input.ClockCost.skip code)

theorem safe (code) (installed : Input.OriginalCode.Installed code) : Input.NoException.Safe code body := by
  have entry := MemoryCostEffects.entry code installed .extend_memory_cost1
  have costSafe := MemoryCostEffects.safe_extend_memory_cost1 code installed
  rw [body_shape]
  refine Input.NoException.scoped_body code _ _ (ofString "extend_memory_cost1") _ _ _ _ _ entry costSafe ?_
  refine Input.NoException.sequence code _ _ (safe_guard code "a") ?_
  apply Input.NoException.declared
  refine Input.NoException.sequence code _ _ (Input.NoException.store code _ _) ?_
  refine Input.NoException.scoped_body code _ _ (ofString "extend_memory_cost1") _ _ _ _ _ entry costSafe ?_
  refine Input.NoException.sequence code _ _ (Input.NoException.store code _ _) ?_
  exact Input.NoException.sequence code _ _ (safe_guard code "b") (Input.NoException.returned code _)

theorem price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code body 42 := by
  have entry := MemoryCostEffects.entry code installed .extend_memory_cost1
  have costPrice := MemoryCostEffects.price_extend_memory_cost1 code installed
  rw [body_shape]
  refine Input.ClockCost.scoped_body code _ _ (ofString "extend_memory_cost1") _ _ _ _ _ 20 21 entry costPrice ?_
  refine Input.ClockCost.sequence code _ _ 0 21 (guard_price code "a") ?_
  apply Input.ClockCost.declared
  refine Input.ClockCost.sequence code _ _ 0 21 (Input.ClockCost.store code _ _) ?_
  refine Input.ClockCost.scoped_body code _ _ (ofString "extend_memory_cost1") _ _ _ _ _ 20 0 entry costPrice ?_
  refine Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _) ?_
  exact Input.ClockCost.sequence code _ _ 0 0 (guard_price code "b") (Input.ClockCost.returned code _)

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.safe
#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.price
