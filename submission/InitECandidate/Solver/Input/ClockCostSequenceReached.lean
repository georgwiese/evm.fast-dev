import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price a suffix only at states reached by an actual normal prefix.
Aborted prefixes retain their own bound and never invoke the suffix rule. -/
theorem sequence_reached_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (front : source.clock-(evaluateHOLFiniteState source first).2.clock≤firstPrice)
    (back : ∀ middle,evaluateHOLFiniteState source first=(none,middle) →
      middle.clock-(evaluateHOLFiniteState middle second).2.clock≤secondPrice) :
    source.clock-(evaluateHOLFiniteState source (.seq first second)).2.clock≤firstPrice+secondPrice := by
  have clock := evaluateHOLFiniteState_clock_le source first
  rw [evaluateHOLFiniteState_seq_line780]
  generalize computed : evaluateHOLFiniteState source first=output at front clock ⊢
  obtain ⟨result,middle⟩ := output
  cases result with
  | none =>
    have next := back middle computed
    have tailClock := evaluateHOLFiniteState_clock_le middle second
    change source.clock-middle.clock≤firstPrice at front
    change middle.clock≤source.clock at clock
    change source.clock-(evaluateHOLFiniteState middle second).2.clock≤firstPrice+secondPrice
    omega
  | some result =>
    change source.clock-middle.clock≤firstPrice at front
    change source.clock-middle.clock≤firstPrice+secondPrice
    omega

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.sequence_reached_current
