import InitECandidate.Solver.Input.NonTimeoutSequenceCall
import InitECandidate.Solver.Input.ClockCostSequenceReached

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Actual non-timeout sequence composition. Each allowance is required
only for the real reached execution; neither premise assumes success. -/
theorem sequence_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (front : ∀ result target,evaluateHOLFiniteState source first=(result,target) → result≠some .timeOut → source.clock-target.clock≤firstPrice)
    (back : ∀ middle,evaluateHOLFiniteState source first=(none,middle) → ∀ result target,
      evaluateHOLFiniteState middle second=(result,target) → result≠some .timeOut → middle.clock-target.clock≤secondPrice)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source (.seq first second)=(result,post))
    (notTimeout : result≠some .timeOut) : source.clock-post.clock≤firstPrice+secondPrice := by
  have firstNotTimeout : (evaluateHOLFiniteState source first).1≠some .timeOut := by
    intro timed
    have whole := sequence_timeout source first second timed
    rw [run] at whole
    exact notTimeout whole
  have firstCost := front (evaluateHOLFiniteState source first).1 (evaluateHOLFiniteState source first).2 rfl firstNotTimeout
  have firstClock := evaluateHOLFiniteState_clock_le source first
  rw [evaluateHOLFiniteState_seq_line780] at run
  generalize observed : evaluateHOLFiniteState source first=output at firstCost firstClock run
  obtain ⟨firstResult,middle⟩ := output
  cases firstResult with
  | none =>
    change evaluateHOLFiniteState middle second=(result,post) at run
    have secondCost := back middle observed result post run notTimeout
    have secondClock := evaluateHOLFiniteState_clock_le middle second
    rw [run] at secondClock
    change post.clock≤middle.clock at secondClock
    change source.clock-middle.clock≤firstPrice at firstCost
    change middle.clock≤source.clock at firstClock
    omega
  | some stopped =>
    have endpoint := congrArg Prod.snd run
    change middle=post at endpoint
    subst post
    change source.clock-middle.clock≤firstPrice at firstCost
    omega

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.sequence_terminating
