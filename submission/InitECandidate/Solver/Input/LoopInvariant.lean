import InitECandidate.Solver.Input.LocalPrefix
import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Carry a current invariant through an actual normal while exit. The
body cannot escape by break/continue, and every actual continuing body
derives its next invariant. No later loop model is assumed. -/
theorem loop_invariant (code) (key : MlS) (condition : ExpHOL 64) (body : ProgHOL 64)
    (safe : LocalPrefix key body) (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word)) →
      word≠0 → current.clock≠0 → ∀ target,
      evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target) → invariant target)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : source.code=code) (valid : invariant source)
    (normal : evaluateHOLFiniteState source (.while condition body)=(none,target)) : invariant target := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock → current.code=code → invariant current →
      evaluateHOLFiniteState current (.while condition body)=(none,target) → invariant target := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq codeEq valid run
      rw [evaluateHOLFiniteState_while_total] at run
      generalize observed : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=value at run
      cases value with
      | none => cases run
      | some value =>
        cases value with
        | rStruct fields => cases run
        | nStruct name fields => cases run
        | val payload =>
          cases payload with
          | word word =>
            simp only at run
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at run
              by_cases zero : current.clock=0
              · rw [if_pos zero] at run
                cases run
              · rw [if_neg zero] at run
                have summary := safe.summary_full (decClockHOLFinite current)
                unfold LocalSummary at summary
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at run summary bodyClock
                obtain ⟨result,middle⟩ := output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) middle result bodyClock] at run
                cases result with
                | none =>
                  have next := step current codeEq valid word observed nonzero zero middle computed
                  have middleCode := (Input.evaluation_fields (decClockHOLFinite current) middle body none computed).2.2.2.trans codeEq
                  have earlier : middle.clock<clock := by change middle.clock≤current.clock-1 at bodyClock; omega
                  exact ih middle.clock earlier middle rfl middleCode next run
                | some result =>
                  cases result with
                  | «break» => exact (summary.2.2.1 rfl).elim
                  | «continue» => exact (summary.2.2.2 rfl).elim
                  | returned value => cases run
                  | error => cases run
                  | timeOut => cases run
                  | exception identifier value => cases run
                  | finalFfi event => cases run
            · rw [if_neg nonzero] at run
              have same : target=current := (Prod.mk.inj run).2.symm
              rw [same]
              exact valid
  exact auxiliary source.clock source rfl installed valid normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.loop_invariant
