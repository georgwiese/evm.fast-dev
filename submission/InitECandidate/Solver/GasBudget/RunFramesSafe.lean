import InitECandidate.Solver.GasBudget.RunFramesProgram
import InitECandidate.Solver.Input.HandledPrefix

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The complete unchanged loop body, including both actual EvmErr handlers,
never escapes its caller through return/break/continue. This is control
coverage only; it proves no opcode cost, gas progress or iteration count. -/
theorem loop_body_safe : Input.HandledPrefix (ofString "setup") loopBody := by
  simp only [loopBody, RootExit.runBody, Guest.guestFn_run_frames, progToHOL, expToHOL, shapeToHOL,
    List.map_cons, List.map_nil, Option.map_none]
  repeat first
    | apply Input.HandledPrefix.seq
    | apply Input.HandledPrefix.ite
    | refine Input.HandledPrefix.dec _ _ _ (by decide) ?_
    | refine Input.HandledPrefix.caught _ _ _ _ (by decide) ?_
    | exact .base .skip
    | exact .base (.globalAssign _ _)
    | exact .base (.assign _ _ (by decide))
    | exact .base (.call none _ _ (by intro name impossible; cases impossible))

theorem loop_body_summary (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    Input.LocalSummary (ofString "setup") loopBody source := loop_body_safe.summary_full source

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.loop_body_safe
#print axioms InitECandidate.Solver.GasBudget.RunFrames.loop_body_summary
