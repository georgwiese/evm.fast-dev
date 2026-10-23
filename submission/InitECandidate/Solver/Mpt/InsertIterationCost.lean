import InitECandidate.Solver.Mpt.InsertNodeCost
import InitECandidate.Solver.Mpt.InsertIterationDispatch

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix GasBudget
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Every whole original iteration outcome, including aborted dispatches,
helper failures and short clocks. Real declarations and go-clear add no
source clock; literal footer stores and assignments add none either. -/
theorem iteration_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (node key level length pointer size go : BitVec 64) (inputs : ScalarInputs source node key level length pointer size)
    (bounded : length.toNat≤64) (before : level.toNat≤length.toNat) (installed : Input.OriginalCode.Installed source.code)
    (goCell : source.locals.lookup (ofString "go")=some (.val (.word go))) :
    source.clock-(evaluateHOLFiniteState source loopBody).2.clock≤565 := by
  have current (name : String) (notRoot : ofString name≠ofString "r") (notNode : ofString name≠ofString "next_node")
      (notSlot : ofString name≠ofString "next_slot") (notLevel : ofString name≠ofString "next_level") (notGo : ofString name≠ofString "go") :
      (dispatchEntry source).locals.lookup (ofString name)=source.locals.lookup (ofString name):=dispatch_saved source name notRoot notNode notSlot notLevel notGo
  have currentInputs : ScalarInputs (dispatchEntry source) node key level length pointer size:=⟨
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.nodeCell,
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.keyCell,
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.levelCell,
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.lengthCell,
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.pointerCell,
    (current _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans inputs.sizeCell⟩
  have front:=node_choice_cost (dispatchEntry source) node key level length pointer size currentInputs bounded before installed
  have price:=Input.ClockCost.sequence_current (dispatchEntry source) nodeChoice afterChoice 565 0 front
    (Input.ClockCost.of_quiet source.code _ (after_choice_quiet source.code))
  have execution:=prefix_execution source go goCell
  have clocks:=congrArg Prod.snd (execution.project (.seq nodeChoice afterChoice))
  change (evaluateHOLFiniteState source (Input.CallPrefix.program iterationActions (.seq nodeChoice afterChoice))).2.clock=
    (evaluateHOLFiniteState (dispatchEntry source) (.seq nodeChoice afterChoice)).2.clock at clocks
  rw [←iteration_shape] at clocks
  rw [clocks]
  exact price

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.iteration_cost
