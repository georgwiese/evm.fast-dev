import InitECandidate.Solver.Mpt.NodeRlpFinishProgram
import InitECandidate.Solver.Input.ConstantCounterCost

namespace InitECandidate.Solver.Mpt.NodeRlpFinish
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scan_body_cost (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code scanBody 2 := by
  rw [scan_shapes.2.1]
  exact Input.ClockCost.scoped_body code (ofString "rl2") .one (ofString "node_ref_len") childArguments (.seq addLength advance)
    NodeRefLen.formals NodeRefLen.body .one 1 0 (NodeRefLen.original_code code installed) (NodeRefLen.body_cost code installed)
    (Input.ClockCost.sequence code _ _ 0 0 (Input.ClockCost.assign code _ _) (Input.ClockCost.assign code _ _))

theorem scan_body_safe : Input.LocalPrefix (ofString "node") scanBody := by
  rw [scan_shapes.2.1]
  exact .decCall _ _ _ _ (by decide) (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide)))

theorem scan_body_advance : Input.CounterFlow.Advances (ofString "i") 1 scanBody := by
  rw [scan_shapes.2.1]
  apply Input.CounterFlow.scoped_call (ofString "i") "rl2" .one _ _ _ 1 (by decide)
  exact Input.CounterFlow.sequence _ _ _ 0 1 (Input.CounterFlow.preserved _ addLength (.assign _ _ (by decide))) (Input.CounterFlow.increment _)

/-- The actual signed16-child reference-length scan costs at most three
source ticks per remaining child, on every outcome. The actual bounded
counter gives strict progress without a future readable-child premise. -/
theorem scan_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤16) :
    source.clock-(evaluateHOLFiniteState source scanLoop).2.clock≤3*(16-index.toNat) := by
  rw [scan_shapes.1]
  exact Input.CounterFlow.constant_loop_cost source.code (ofString "i") (ofString "node") scanBody 2 16 (by decide)
    (scan_body_cost source.code installed) scan_body_advance scan_body_safe source index rfl indexCell bounded

end InitECandidate.Solver.Mpt.NodeRlpFinish

#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_body_cost
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_body_safe
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_body_advance
#print axioms InitECandidate.Solver.Mpt.NodeRlpFinish.scan_cost
