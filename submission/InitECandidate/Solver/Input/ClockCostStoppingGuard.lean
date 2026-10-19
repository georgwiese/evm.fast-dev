import InitECandidate.Solver.Input.NoFallthrough
import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A selected branch that cannot fall through excludes the later suffix,
so the actual conditional sequence costs their maximum rather than sum. -/
theorem stopping_guard (code) (test : ExpHOL 64) (first second : ProgHOL 64) (firstPrice secondPrice : Nat)
    (stops : NoFallthrough first) (front : Bound code first firstPrice) (back : Bound code second secondPrice) :
    Bound code (.seq (.ite test first .skip) second) (max firstPrice secondPrice) := by
  classical
  intro source installed
  have firstCost := front source installed
  have secondCost := back source installed
  have noNormal := stops source
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
  generalize observed : @evalHOLExact 64 Guest.HostMemory _ source.toExact
    (fun address => Classical.propDecidable (source.memaddrs address)) test = value
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
        by_cases zero : word = 0
        · rw [if_pos zero, evaluateHOLFiniteState_skip]
          exact secondCost.trans (Nat.le_max_right _ _)
        · rw [if_neg zero]
          generalize computed : evaluateHOLFiniteState source first = output at firstCost noNormal ⊢
          obtain ⟨result, target⟩ := output
          cases result with
          | none => exact (noNormal rfl).elim
          | some result => exact firstCost.trans (Nat.le_max_left _ _)

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.stopping_guard
