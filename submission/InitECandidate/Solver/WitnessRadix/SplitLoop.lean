import InitECandidate.Solver.WitnessRadix.SplitCountExecution
import InitECandidate.Solver.WitnessRadix.UnaryLoop

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch SplitScope

theorem post_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) :
    (post source context).clock = source.clock - 3 * context.input.length := by
  change source.clock - context.input.length - 2 * context.input.length = source.clock - 3 * context.input.length
  omega

theorem main_body_split {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) (many : 1 < context.input.length) :
    evaluateHOLFiniteState source BuildEntry.mainBody = (none, post source context) := by
  classical
  have test := UnaryProgram.not_terminal source context.input.length context.position premises.small many premises.inside
    premises.locals.countLocal premises.locals.bitLocal
  have skipped : evaluateHOLFiniteState source (.ite TerminalProgram.terminalTest TerminalProgram.terminalCode .skip) =
      (none, source) := by
    simp only [eval] at test
    rw [evaluateHOLFiniteState_ite, test]
    simp
  rw [TerminalProgram.main_body_shape, StateSteps.next_sequence source source _ _ skipped (Nat.le_refl _)]
  exact execute source context premises

/-- Complete nonterminal two-way outer iteration. Its exact source-clock
cost is 3*input.length + 1: count, scatter, copy and the outer while step. -/
theorem main_loop_split {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) (many : 1 < context.input.length)
    (enough : 3 * context.input.length + 1 ≤ source.clock) :
    evaluateHOLFiniteState source BuildEntry.mainLoop =
      evaluateHOLFiniteState (post (decClockHOLFinite source) context) BuildEntry.mainLoop := by
  classical
  let entry := decClockHOLFinite source
  have entryPremises : Inputs entry context :=
    ⟨premises.inside, premises.small, premises.fits, premises.allocation,
      (by change 3 * context.input.length ≤ source.clock - 1; omega), premises.splitZero, premises.splitOne,
      task_locals_of_lookup source entry context (by intros; rfl) premises.locals,
      SplitProgram.mapped_of_field (source := source) (target := entry) rfl premises.mapped,
      ScatterProgram.ready_of_fields source entry rfl rfl rfl _ _ _ _ _ _ _ _ premises.ready⟩
  have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) BuildEntry.mainBody =
      (none, post (decClockHOLFinite source) context) := main_body_split entry context entryPremises many
  have positive : source.clock ≠ 0 := by omega
  rw [TerminalProgram.main_loop_shape, evaluateHOLFiniteState_while_total]
  simp only [evalHOLFinite, evalHOLExact]
  rw [if_pos (by decide)]
  simp only [if_neg positive, bodyRun]
  rw [StateSteps.fixed_clock entry (post entry context) _ (by rw [post_clock]; omega)]

theorem iteration_clock {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) :
    (post (decClockHOLFinite source) context).clock = source.clock - (3 * context.input.length + 1) := by
  rw [post_clock]
  change source.clock - 1 - 3 * context.input.length = _
  omega

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.main_loop_split
#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.iteration_clock
