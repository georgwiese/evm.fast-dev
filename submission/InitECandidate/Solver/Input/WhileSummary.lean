import InitECandidate.Solver.Input.WhileControlBody
import InitECandidate.Solver.Input.HandledPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem while_none_step_summary {F : Type} (source target : PanSemStateFiniteExact 64 F) (key : MlS)
    (condition : ExpHOL 64) (body : ProgHOL 64) (summary : LocalSummary key body (decClockHOLFinite source))
    (read : eval source condition = some (.val (.word 1#64)))
    (normal : evaluateHOLFiniteState source (.while condition body) = (none, target)) :
    1 ≤ source.clock ∧ ∃ middle,
      evaluateHOLFiniteState (decClockHOLFinite source) body = (none, middle) ∧
      evaluateHOLFiniteState middle (.while condition body) = (none, target) ∧ middle.clock ≤ source.clock - 1 := by
  obtain ⟨positive, middle, result, bodyRun, control, bounded⟩ := while_control_body source target condition body read none .next normal
  unfold LocalSummary at summary
  rw [bodyRun] at summary
  have bodyNone : result = none := by
    cases control with
    | next => rfl
    | returned value => exact (summary.2.1 value rfl).elim
    | breaks => exact (summary.2.2.1 rfl).elim
    | continues => exact (summary.2.2.2 rfl).elim
  rw [bodyNone] at bodyRun
  have tailRun := normal
  rw [evaluateHOLFiniteState_while_total] at tailRun
  simp only [eval, evalHOLFinite] at read tailRun
  rw [read] at tailRun
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide), if_neg (show source.clock ≠ 0 from by omega)] at tailRun
  rw [bodyRun, WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) middle none bounded] at tailRun
  exact ⟨positive, middle, bodyRun, tailRun, bounded⟩

theorem HandledPrefix.while_none_step {F : Type} {key : MlS} {body : ProgHOL 64} (safe : HandledPrefix key body)
    (source target : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64)
    (read : eval source condition = some (.val (.word 1#64)))
    (normal : evaluateHOLFiniteState source (.while condition body) = (none, target)) :
    1 ≤ source.clock ∧ ∃ middle,
      evaluateHOLFiniteState (decClockHOLFinite source) body = (none, middle) ∧
      evaluateHOLFiniteState middle (.while condition body) = (none, target) ∧ middle.clock ≤ source.clock - 1 :=
  while_none_step_summary source target key condition body (safe.summary_full (decClockHOLFinite source)) read normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.while_none_step_summary
#print axioms InitECandidate.Solver.Input.HandledPrefix.while_none_step
