import InitECandidate.Solver.Mpt.CollapseBranchProgram
import InitECandidate.Solver.Input.ConstantCounterCost
import InitECandidate.Solver.Input.LocalEffectsLoop

namespace InitECandidate.Solver.Mpt.CollapseBranch
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scan_body_safe (key : MlS) (notCount : key≠ofString "count") (notIndex : key≠ofString "idx") (notCounter : key≠ofString "i") :
    Input.LocalPrefix key scanBody := by
  rw [scan_shapes.2.1,scan_shapes.2.2.1,scan_shapes.2.2.2,selected]
  exact .seq (.ite _ (.seq (.assign _ _ notCount) (.assign _ _ notIndex)) .skip) (.assign _ _ notCounter)

theorem scan_body_effects (code) : Input.LocalEffects.Preserves code scanBody ∧ Input.QuietClock.Preserves code scanBody := by
  rw [scan_shapes.2.1,scan_shapes.2.2.1,scan_shapes.2.2.2,selected]
  constructor
  · repeat first
      | apply Input.LocalEffects.sequence
      | apply Input.LocalEffects.conditional
      | exact Input.LocalEffects.assign code _ _
      | exact Input.LocalEffects.skip code
  · repeat first
      | apply Input.QuietClock.sequence
      | apply Input.QuietClock.conditional
      | exact Input.QuietClock.assign code _ _
      | exact Input.QuietClock.skip code

theorem scan_advances : Input.CounterFlow.Advances (ofString "i") 1 scanBody := by
  have safe : Input.LocalPrefix (ofString "i") scanChoice:=by
    rw [scan_shapes.2.2.1,selected]
    exact .ite _ (.seq (.assign _ _ (by decide)) (.assign _ _ (by decide))) .skip
  rw [scan_shapes.2.1,scan_shapes.2.2.2]
  exact Input.CounterFlow.sequence (ofString "i") scanChoice _ 0 1 (Input.CounterFlow.preserved _ _ safe) (Input.CounterFlow.increment _)

/-- The fixed signed sixteen-child scan costs only its remaining loop
ticks on every outcome, including unmapped or malformed child reads. -/
theorem scan_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : BitVec 64)
    (cell : source.locals.lookup (ofString "i")=some (.val (.word index))) (bounded : index.toNat≤16) :
    source.clock-(evaluateHOLFiniteState source scan).2.clock≤16-index.toNat := by
  rw [scan_shapes.1]
  simpa only [scanTest,localVar,Nat.zero_add,Nat.one_mul] using Input.CounterFlow.constant_loop_cost source.code (ofString "i") (ofString "node") scanBody 0 16 (by decide)
    (Input.ClockCost.of_quiet source.code scanBody (scan_body_effects source.code).2) scan_advances
    (scan_body_safe _ (by decide) (by decide) (by decide)) source index rfl cell bounded

end InitECandidate.Solver.Mpt.CollapseBranch

#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_body_safe
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_body_effects
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_advances
#print axioms InitECandidate.Solver.Mpt.CollapseBranch.scan_cost
