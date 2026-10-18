import InitECandidate.Solver.Input.LocalPrefix

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

theorem sequence_none {F : Type} (source target : PanSemStateFiniteExact 64 F) (first second : ProgHOL 64)
    (normal : evaluateHOLFiniteState source (.seq first second) = (none, target)) :
    ∃ middle, evaluateHOLFiniteState source first = (none, middle) ∧ evaluateHOLFiniteState middle second = (none, target) := by
  rw [evaluateHOLFiniteState_seq_line780] at normal
  generalize computed : evaluateHOLFiniteState source first = output at normal
  obtain ⟨result, middle⟩ := output
  cases result with
  | none => exact ⟨middle, rfl, normal⟩
  | some result => cases normal

/-- Invert one taken original loop iteration from an actual normal loop
outcome. Caller-local safety excludes a hidden break or continue; the
iteration clock and genuine body/tail runs are derived from execution. -/
theorem while_none_step {F : Type} (source target : PanSemStateFiniteExact 64 F) (key : MlS)
    (condition : ExpHOL 64) (body : ProgHOL 64) (safe : LocalPrefix key body)
    (read : eval source condition = some (.val (.word 1#64)))
    (normal : evaluateHOLFiniteState source (.while condition body) = (none, target)) :
    1 ≤ source.clock ∧ ∃ middle,
      evaluateHOLFiniteState (decClockHOLFinite source) body = (none, middle) ∧
      evaluateHOLFiniteState middle (.while condition body) = (none, target) ∧ middle.clock ≤ source.clock - 1 := by
  classical
  rw [evaluateHOLFiniteState_while_total] at normal
  simp only [eval, evalHOLFinite] at read normal
  rw [read] at normal
  simp only [if_pos (show (1#64 : BitVec 64) ≠ 0 from by decide)] at normal
  by_cases zero : source.clock = 0
  · rw [if_pos zero] at normal
    cases normal
  · rw [if_neg zero] at normal
    let entry := decClockHOLFinite source
    have summary := safe.summary_full entry
    have clock := evaluateHOLFiniteState_clock_le entry body
    unfold LocalSummary at summary
    generalize computed : evaluateHOLFiniteState entry body = output at normal summary clock
    obtain ⟨result, middle⟩ := output
    rw [WitnessRadix.StateSteps.fixed_clock entry middle result clock] at normal
    cases result with
    | none => exact ⟨by omega, middle, rfl, normal, clock⟩
    | some result =>
      cases result with
      | returned value => exact (summary.2.1 value rfl).elim
      | «break» => exact (summary.2.2.1 rfl).elim
      | «continue» => exact (summary.2.2.2 rfl).elim
      | error => cases normal
      | timeOut => cases normal
      | exception identifier payload => cases normal
      | finalFfi event => cases normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.sequence_none
#print axioms InitECandidate.Solver.Input.while_none_step
