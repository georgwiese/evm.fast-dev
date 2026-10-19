import InitECandidate.Solver.GasBudget.StackPushGrowthNormal
import InitECandidate.Solver.Input.ControlContinue
import InitECandidate.Solver.Input.SequenceControl

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

theorem grow_control_none (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : BitVec 64)
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (bounded : capacity.toNat ≤ 512) (result : Option (PanSemResultExact 64)) (control : Input.ControlResult result)
    (run : evaluateHOLFiniteState source growBranch = (result, target)) : result = none := by
  have below : ¬1024#64 ≤ capacity := by change ¬1024 ≤ capacity.toNat; omega
  have guardRun : evaluateHOLFiniteState source growGuard = (none, source) := by
    rw [growGuard, evaluateHOLFiniteState_ite]
    simp [evalHOLExact, toExact, localVar, capLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, below,
      evaluateHOLFiniteState_skip]
  rw [grow_branch_shape, StateSteps.next_sequence _ _ _ _ guardRun (Nat.le_refl _)] at run
  have safe : Input.LocalPrefix (ofString "sp")
      (.dec (ofString "ncap") .one (.panop .mul [localVar "cap", .const 2#64]) (.seq growClamp growAllocate)) := by
    unfold growClamp growAllocate growCopy growStores
    exact .dec _ _ _ (by decide) (.seq (.ite _ (.assign _ _ (by decide)) .skip)
      (.decCall _ _ _ _ (by decide) (.seq (.call none _ _ (by intro name impossible; cases impossible))
        (.seq (.store _ _) (.store _ _)))))
  exact safe.control_none source target result control run

theorem growth_taken (source : PanSemStateFiniteExact 64 Guest.HostMemory) (capacity : BitVec 64)
    (spLocal : source.locals.lookup (ofString "sp") = some (.val (.word capacity)))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word capacity))) :
    evaluateHOLFiniteState source growth = evaluateHOLFiniteState source growBranch := by
  rw [choice_shape, evaluateHOLFiniteState_ite]
  simp [evalHOLExact, toExact, localVar, spLocal, capLocal, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.grow_control_none
#print axioms InitECandidate.Solver.GasBudget.StackPush.growth_taken
