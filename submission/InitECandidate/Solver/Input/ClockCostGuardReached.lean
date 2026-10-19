import InitECandidate.Solver.Input.ClockCostCurrentGuard

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price a suffix only when the actual guard passes. The true failing
branch stops, and the real skipped guard supplies its unchanged entry state. -/
theorem stopping_guard_reached (source : PanSemStateFiniteExact 64 Guest.HostMemory) (test : ExpHOL 64)
    (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (stops : (evaluateHOLFiniteState source first).1≠none)
    (front : source.clock-(evaluateHOLFiniteState source first).2.clock≤firstPrice)
    (back : evaluateHOLFiniteState source (.ite test first .skip)=(none,source) →
      source.clock-(evaluateHOLFiniteState source second).2.clock≤secondPrice) :
    source.clock-(evaluateHOLFiniteState source (.seq (.ite test first .skip) second)).2.clock≤max firstPrice secondPrice := by
  rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address=>Classical.propDecidable (source.memaddrs address)) test=value
  cases value with
  | none => simp
  | some value =>
    cases value with
    | rStruct fields => simp
    | nStruct name fields => simp
    | val payload =>
      cases payload with
      | word word =>
        simp only
        by_cases zero : word=0
        · rw [if_pos zero,evaluateHOLFiniteState_skip]
          have passed : evaluateHOLFiniteState source (.ite test first .skip)=(none,source) := by
            rw [evaluateHOLFiniteState_ite,observed]
            simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact (back passed).trans (Nat.le_max_right _ _)
        · rw [if_neg zero]
          generalize computed : evaluateHOLFiniteState source first=output at front stops ⊢
          obtain ⟨result,target⟩ := output
          cases result with
          | none => exact (stops rfl).elim
          | some result => exact front.trans (Nat.le_max_left _ _)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.stopping_guard_reached
