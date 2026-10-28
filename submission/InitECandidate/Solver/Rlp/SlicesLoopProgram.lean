import InitECandidate.Solver.Rlp.SlicesSyntax
import InitECandidate.Solver.Rlp.UncheckedCost
import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.Input.CounterLoopCost

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem stores_price (code) : Input.ClockCost.Bound code stores 0 :=
  Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.store code _ _)
      (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _)))
theorem loop_body_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code loopBody 10 :=
  Unchecked.scoped_price code installed (ofString "total") .one _ stores 0 (stores_price code)

theorem loop_body_safe : Input.LocalPrefix (ofString "count") loopBody := by
  unfold loopBody stores advances
  exact .decCall _ _ _ _ (by decide) (.seq (.store _ _) (.seq (.store _ _) (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))))

theorem loop_body_advances : Input.CounterFlow.Advances (ofString "i") 1 loopBody := by
  unfold loopBody stores advances
  apply Input.CounterFlow.scoped_call _ _ _ _ _ _ 1 (by decide)
  apply Input.CounterFlow.sequence _ _ _ 0 1
  · exact Input.CounterFlow.preserved _ _ (.store _ _)
  · apply Input.CounterFlow.sequence _ _ _ 0 1
    · exact Input.CounterFlow.preserved _ _ (.store _ _)
    · apply Input.CounterFlow.sequence _ _ _ 0 1
      · exact Input.CounterFlow.preserved _ _ (.assign _ _ (by decide))
      · exact Input.CounterFlow.increment _

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.stores_price
#print axioms InitECandidate.Solver.Rlp.Slices.loop_body_price
#print axioms InitECandidate.Solver.Rlp.Slices.loop_body_safe
#print axioms InitECandidate.Solver.Rlp.Slices.loop_body_advances
