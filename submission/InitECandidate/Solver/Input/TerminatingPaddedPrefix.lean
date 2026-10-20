import InitECandidate.Solver.Input.EvaluationClockSub
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real sufficiently padded prefix, including hashes with event/memory
effects, determines the actual reached prefix of any terminating execution.
The remaining clock is derived from termination of the enclosing sequence. -/
theorem terminating_padded_prefix {F : Type} (source post middle : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (padding : Nat) (result : Option (PanSemResultExact 64))
    (prefixRun : evaluateHOLFiniteState {source with clock := source.clock + padding} first = (none,middle))
    (normal : evaluateHOLFiniteState source (.seq first second) = (result,post))
    (notTimeout : result ≠ some .timeOut) :
    padding ≤ middle.clock ∧
      evaluateHOLFiniteState source first = (none,{middle with clock := middle.clock - padding}) ∧
      evaluateHOLFiniteState {middle with clock := middle.clock - padding} second = (result,post) := by
  have padded := panPropsEvaluateAddClockEq (.seq first second) source result post padding ⟨normal,notTimeout⟩
  rw [evaluateHOLFiniteState_seq_line780] at padded
  simp only [prefixRun] at padded
  have remaining := evaluateHOLFiniteState_clock_le middle second
  rw [padded] at remaining
  change post.clock + padding ≤ middle.clock at remaining
  have enough : padding ≤ middle.clock := by omega
  have actual := evaluation_clock_sub {source with clock := source.clock + padding} middle first none padding prefixRun enough (by intro impossible; cases impossible)
  simp only [Nat.add_sub_cancel_right] at actual
  rw [evaluateHOLFiniteState_seq_line780] at normal
  simp only [actual] at normal
  exact ⟨enough,actual,normal⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.terminating_padded_prefix
