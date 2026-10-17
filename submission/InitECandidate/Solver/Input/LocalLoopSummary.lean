import InitECandidate.Solver.WitnessRadix.StateSteps
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Caller-local preservation on continuation and absence of escaping return,
break or continue. Errors/exceptions/timeouts are unrestricted. -/
def LocalSummary {F : Type} (key : MlS) (program : ProgHOL 64) (source : PanSemStateFiniteExact 64 F) : Prop :=
  ((evaluateHOLFiniteState source program).1 = none →
    (evaluateHOLFiniteState source program).2.locals.lookup key = source.locals.lookup key) ∧
  (∀ value, (evaluateHOLFiniteState source program).1 ≠ some (.returned value)) ∧
  (evaluateHOLFiniteState source program).1 ≠ some .break ∧
  (evaluateHOLFiniteState source program).1 ≠ some .continue

/-- Actual finite-clock while evaluation preserves a saved local when every
body continuation does. This bounds no iteration count or runtime: the clock
is used only as the evaluator's induction parameter. -/
theorem while_local_summary {F : Type} (key : MlS) (condition : ExpHOL 64) (body : ProgHOL 64)
    (bodySummary : ∀ source : PanSemStateFiniteExact 64 F, LocalSummary key body source)
    (source : PanSemStateFiniteExact 64 F) : LocalSummary key (.while condition body) source := by
  classical
  generalize rankEq : source.clock = rank
  induction rank using Nat.strongRecOn generalizing source with
  | ind rank ih =>
    unfold LocalSummary
    rw [evaluateHOLFiniteState_while_total]
    cases read : @evalHOLFinite 64 F _ source (fun address => Classical.propDecidable (source.memaddrs address)) condition with
    | none => simp
    | some value =>
      cases value with
      | rStruct fields => simp
      | nStruct name fields => simp
      | val payload =>
        cases payload with
        | word word =>
          simp only
          by_cases active : word ≠ 0
          · rw [if_pos active]
            by_cases zero : source.clock = 0
            · simp [zero]
            · rw [if_neg zero]
              let entry := decClockHOLFinite source
              have info := bodySummary entry
              unfold LocalSummary at info
              have clock := evaluateHOLFiniteState_clock_le entry body
              generalize bodyRun : evaluateHOLFiniteState entry body = output at info clock ⊢
              obtain ⟨result, next⟩ := output
              have nextClock : next.clock ≤ entry.clock := clock
              rw [WitnessRadix.StateSteps.fixed_clock entry next result nextClock]
              cases result with
              | none =>
                have smaller : next.clock < rank := by
                  change next.clock ≤ source.clock - 1 at nextClock
                  omega
                have tail := ih next.clock smaller next rfl
                exact ⟨fun normal => (tail.1 normal).trans (info.1 rfl), tail.2⟩
              | some result =>
                cases result with
                | returned value => exact False.elim (info.2.1 value rfl)
                | «break» => exact False.elim (info.2.2.1 rfl)
                | «continue» => exact False.elim (info.2.2.2 rfl)
                | error => simp
                | timeOut => simp
                | exception identifier payload => simp
                | finalFfi event => simp
          · rw [if_neg active]
            simp

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.while_local_summary
