import InitECandidate.Solver.Input.EvaluationClockSub
import Flapjack.Pancake.Semantics.PanProps.EvaluateAddClockEq

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine padded prefix and an actual enclosing non-timeout run derive
funding for the prefix's actual cost, including variable-cost rejection.
The prefix may either continue or stop; its real memory/FFI effects survive. -/
theorem terminating_padded_sequence {F : Type} (source post middle : PanSemStateFiniteExact 64 F)
    (first second : ProgHOL 64) (padding : Nat) (prefixResult result : Option (PanSemResultExact 64))
    (prefixRun : evaluateHOLFiniteState {source with clock := source.clock + padding} first = (prefixResult,middle))
    (run : evaluateHOLFiniteState source (.seq first second) = (result,post)) (notTimeout : result ≠ some .timeOut) :
    padding ≤ middle.clock ∧ evaluateHOLFiniteState source first = (prefixResult,{middle with clock := middle.clock - padding}) := by
  have whole := panPropsEvaluateAddClockEq (.seq first second) source result post padding ⟨run,notTimeout⟩
  rw [evaluateHOLFiniteState_seq_line780,prefixRun] at whole
  have funded : padding ≤ middle.clock := by
    cases prefixResult with
    | none =>
      dsimp only at whole
      have clock := evaluateHOLFiniteState_clock_le middle second
      rw [whole] at clock
      change post.clock + padding ≤ middle.clock at clock
      omega
    | some stopped =>
      dsimp only at whole
      have clock := congrArg (fun output => output.2.clock) whole
      change middle.clock = post.clock + padding at clock
      omega
  have prefixNotTimeout : prefixResult ≠ some .timeOut := by
    intro bad
    rw [bad] at whole
    have same := congrArg Prod.fst whole
    change some PanSemResultExact.timeOut = result at same
    exact notTimeout same.symm
  have lowered := evaluation_clock_sub {source with clock := source.clock + padding} middle first prefixResult padding prefixRun funded prefixNotTimeout
  have sourceEq : {source with clock := source.clock + padding - padding} = source := by simp
  rw [sourceEq] at lowered
  exact ⟨funded,lowered⟩

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.terminating_padded_sequence
