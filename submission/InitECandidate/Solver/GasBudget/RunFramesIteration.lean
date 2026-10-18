import InitECandidate.Solver.GasBudget.RunFramesSafe
import InitECandidate.Solver.Input.WhileSummary

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real taken iteration of any normal run_frames loop, covering opcode
and child handlers as well as immediate completion. This extracts execution
and its consumed loop clock; it is not a gas rank or iteration-count bound. -/
theorem iteration_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (goWord : BitVec 64)
    (go : source.locals.lookup (ofString "go") = some (.val (.word goWord))) (nonzero : goWord ≠ 0#64)
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    1 ≤ source.clock ∧ ∃ middle,
      evaluateHOLFiniteState (decClockHOLFinite source) loopBody = (none, middle) ∧
      evaluateHOLFiniteState middle loop = (none, target) ∧ middle.clock ≤ source.clock - 1 := by
  have read : eval source condition = some (.val (.word 1#64)) := by
    simp [eval, condition, evalHOLExact, localVar, toExact, go, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
  exact loop_body_safe.while_none_step source target condition read normal

theorem finished (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (go : source.locals.lookup (ofString "go") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source loop = (none, source) := by
  have read : eval source condition = some (.val (.word 0#64)) := by
    simp [eval, condition, evalHOLExact, localVar, toExact, go, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [loop, evaluateHOLFiniteState_while_total]
  simp only [eval, evalHOLFinite] at read ⊢
  rw [read]
  simp

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.iteration_normal
#print axioms InitECandidate.Solver.GasBudget.RunFrames.finished
