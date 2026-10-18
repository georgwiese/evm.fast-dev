import InitECandidate.Solver.GasBudget.RunFramesCaughtDispatch
import InitECandidate.Solver.Input.HandledPrefix

namespace InitECandidate.Solver.GasBudget.RunFrames
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Concrete current header words selecting the active-opcode path. -/
def ActiveHeader (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont running pc length : BitVec 64) : Prop :=
  source.globals.lookup (ofString "ev") = some (.val (.word frame)) ∧
  source.globals.lookup (ofString "cur_cont") = some (.val (.word cont)) ∧
  source.memaddrs (cont + 32#64) ∧ source.memory (cont + 32#64) = .word 0#64 ∧
  source.memaddrs (frame + 104#64) ∧ source.memory (frame + 104#64) = .word running ∧ running ≠ 0#64 ∧
  source.memaddrs (frame + 0#64) ∧ source.memory (frame + 0#64) = .word pc ∧
  source.memaddrs (frame + 56#64) ∧ source.memory (frame + 56#64) = .word length ∧ pc < length

/-- The original active guard path reaches the real opcode branch, with its
real pc binding. Valid words/mappings are current-state facts, not executions. -/
theorem active_head_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame cont running pc length : BitVec 64)
    (header : ActiveHeader source frame cont running pc length) :
    evaluateHOLFiniteState source head =
      (let output := evaluateHOLFiniteState (bind source "pc" pc) opcodeBranch
       (output.1, restore source "pc" output.2)) := by
  obtain ⟨ev, continuation, markedMapped, markedCell, runningMapped, runningCell, nonzero, pcMapped, pcCell, lengthMapped, lengthCell, inside⟩ := header
  have markedRead := Input.global_field_read source "cur_cont" cont 32#64 0#64 continuation markedMapped markedCell
  change eval source (RootExit.recordLoad 32#64) = some (.val (.word 0#64)) at markedRead
  have markedTest : eval source markedCondition = some (.val (.word 0#64)) := by
    simp only [eval] at markedRead
    simp [eval, markedCondition, evalHOLExact, markedRead, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have runningRead := frame_read source frame 104#64 running ev runningMapped runningCell
  have runningTest : eval source haltedCondition = some (.val (.word 0#64)) := by
    simp only [eval] at runningRead
    simp [eval, haltedCondition, evalHOLExact, runningRead, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, nonzero]
  let entered := bind source "pc" pc
  have pcLocal : entered.locals.lookup (ofString "pc") = some (.val (.word pc)) := bind_lookup_same _ _ _
  have lengthRead := frame_read entered frame 56#64 length ev lengthMapped lengthCell
  have endTest : eval entered codeEndCondition = some (.val (.word 0#64)) := by
    simp only [eval] at lengthRead
    simp [eval, codeEndCondition, localVar, evalHOLExact, toExact, pcLocal, lengthRead, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, inside]
  have restRun : evaluateHOLFiniteState entered (.ite codeEndCondition markDone opcodeBranch) = evaluateHOLFiniteState entered opcodeBranch := by
    simp only [eval] at endTest
    rw [evaluateHOLFiniteState_ite, endTest]
    simp
  have pcRead := frame_read source frame 0#64 pc ev pcMapped pcCell
  have pcRun := Input.ScalarScope.declare_execute source (evaluateHOLFiniteState entered opcodeBranch).2 "pc" (frameLoad 0#64) pc
    (.ite codeEndCondition markDone opcodeBranch) (evaluateHOLFiniteState entered opcodeBranch).1 pcRead restRun
  simp only [eval] at markedTest runningTest
  rw [head_shape, evaluateHOLFiniteState_ite, markedTest]
  change evaluateHOLFiniteState source dispatchBranch = _
  rw [dispatch_shape, evaluateHOLFiniteState_ite, runningTest]
  change evaluateHOLFiniteState source pcBranch = _
  rw [pc_shape, pcRun]

theorem opcode_done_safe : Input.HandledPrefix (ofString "done") opcodeBranch := by
  rw [opcode_shape]
  unfold caughtDispatch opcodeHandler
  exact .dec _ _ _ (by decide) (.caught _ _ _ _ (by decide) (.base (.call none _ _ (by intro name impossible; cases impossible))))

theorem opcode_done_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState source opcodeBranch = (none, post)) :
    post.locals.lookup (ofString "done") = source.locals.lookup (ofString "done") := by
  have safe := opcode_done_safe.summary_full source
  unfold Input.LocalSummary at safe
  rw [run] at safe
  exact safe.1 rfl

end InitECandidate.Solver.GasBudget.RunFrames

#print axioms InitECandidate.Solver.GasBudget.RunFrames.active_head_execute
#print axioms InitECandidate.Solver.GasBudget.RunFrames.opcode_done_safe
#print axioms InitECandidate.Solver.GasBudget.RunFrames.opcode_done_normal
