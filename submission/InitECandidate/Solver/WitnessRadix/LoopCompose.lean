import InitECandidate.Solver.WitnessRadix.InvariantSplit
import InitECandidate.Solver.WitnessRadix.InvariantUnary
import InitECandidate.Solver.WitnessRadix.InvariantFinish

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

def control {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite { state with memory := fun _ => .word 0#64, clock := 0 }

theorem control_of_frame {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (frame : emptyLocalsHOLFinite source = emptyLocalsHOLFinite target) : control source = control target := by
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F =>
    { state with memory := fun _ => .word 0#64, clock := 0 }) frame
  simpa only [control, emptyLocalsHOLFinite] using updated

theorem unary_control {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) :
    control (unaryPost source context) = control source := rfl

theorem split_control {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) :
    control (SplitCount.post source context) = control source := rfl

theorem resume_control {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (task : PendingStack.Task) (ordinal : Nat) :
    control (resumePost source context task ordinal) = control source := rfl

theorem loop_next {F : Type} (source target : PanSemStateFiniteExact 64 F) (flow : Option (PanSemResultExact 64))
    (resumable : flow = none ∨ flow = some .continue) (positive : source.clock ≠ 0)
    (body : evaluateHOLFiniteState (decClockHOLFinite source) BuildEntry.mainBody = (flow, target))
    (clock : target.clock ≤ (decClockHOLFinite source).clock) :
    evaluateHOLFiniteState source BuildEntry.mainLoop = evaluateHOLFiniteState target BuildEntry.mainLoop := by
  classical
  rcases resumable with rfl | rfl
  all_goals
    rw [TerminalProgram.main_loop_shape, evaluateHOLFiniteState_while_total]
    simp only [evalHOLFinite, evalHOLExact]
    rw [if_pos (by decide)]
    simp only [if_neg positive, body]
    rw [StateSteps.fixed_clock (decClockHOLFinite source) target _ clock]

theorem loop_return {F : Type} (source target : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (positive : source.clock ≠ 0)
    (body : evaluateHOLFiniteState (decClockHOLFinite source) BuildEntry.mainBody = (some (.returned value), target))
    (clock : target.clock ≤ (decClockHOLFinite source).clock) :
    evaluateHOLFiniteState source BuildEntry.mainLoop = (some (.returned value), target) := by
  classical
  rw [TerminalProgram.main_loop_shape, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact]
  rw [if_pos (by decide)]
  simp only [if_neg positive, body]
  rw [StateSteps.fixed_clock (decClockHOLFinite source) target _ clock]

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.loop_next
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.loop_return
