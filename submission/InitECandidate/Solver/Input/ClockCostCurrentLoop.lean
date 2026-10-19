import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Price an actual loop with a body allowance derived only at states
satisfying its current invariant. This is a composition rule, not an instantiated
program bound. Price an actual loop from a current-state natural rank. The transition
premise concerns the actual body output, including continue; aborted bodies
need no future invariant. Timeouts and every other outcome are included. -/
theorem ranked_loop_current (code) (test : ExpHOL 64) (body : ProgHOL 64) (price : Nat)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (rank : PanSemStateFiniteExact 64 Guest.HostMemory → Nat)
    (priced : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      source.code = code → invariant source → ∀ word : BitVec 64,
      evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test = some (.val (.word word)) →
      word ≠ 0 → source.clock ≠ 0 →
      source.clock - 1 - (evaluateHOLFiniteState (decClockHOLFinite source) body).2.clock ≤ price)
    (progress : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      source.code = code → invariant source →
      ∀ word : BitVec 64,
      evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test = some (.val (.word word)) →
      word ≠ 0 → 0 < rank source ∧
        (source.clock ≠ 0 →
          let output := evaluateHOLFiniteState (decClockHOLFinite source) body
          (output.1 = none ∨ output.1 = some .continue) → invariant output.2 ∧ rank output.2 < rank source))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (installed : source.code = code) (valid : invariant source) :
    source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤ (price + 1) * rank source := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory),
      source.clock = clock → source.code = code → invariant source →
      source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤ (price + 1) * rank source := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source clockEq installed valid
      rw [evaluateHOLFiniteState_while_total]
      generalize observed : evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test = value
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
            by_cases nonzero : word ≠ 0
            · rw [if_pos nonzero]
              obtain ⟨positiveRank, transition⟩ := progress source installed valid word observed nonzero
              by_cases zero : source.clock = 0
              · rw [if_pos zero]
                simp [zero]
              · rw [if_neg zero]
                have bodyCost := priced source installed valid word observed nonzero zero
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite source) body
                have transition := transition zero
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite source) body = output at bodyCost bodyClock transition ⊢
                obtain ⟨result, target⟩ := output
                have fixed := WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite source) target result bodyClock
                simp only [fixed]
                change source.clock - 1 - target.clock ≤ price at bodyCost
                change target.clock ≤ source.clock - 1 at bodyClock
                have targetCode : target.code = code :=
                  (Input.evaluation_fields (decClockHOLFinite source) target body result computed).2.2.2.trans installed
                have onePrice : price + 1 ≤ (price + 1) * rank source := by
                  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (price + 1) positiveRank
                have stopped : source.clock - target.clock ≤ (price + 1) * rank source := by omega
                have tail : (result = none ∨ result = some .continue) →
                    source.clock - (evaluateHOLFiniteState target (.while test body)).2.clock ≤ (price + 1) * rank source := by
                  intro continuing
                  obtain ⟨targetValid, smaller⟩ := transition continuing
                  change rank target < rank source at smaller
                  have earlier : target.clock < clock := by omega
                  have tailCost := ih target.clock earlier target rfl targetCode targetValid
                  have tailClock := evaluateHOLFiniteState_clock_le target (.while test body)
                  have budget := Nat.mul_le_mul_left (price + 1) (show rank target + 1 ≤ rank source by omega)
                  rw [Nat.mul_add, Nat.mul_one] at budget
                  omega
                cases result with
                | none => exact tail (Or.inl rfl)
                | some result =>
                  cases result <;> first | exact tail (Or.inr rfl) | exact stopped
            · rw [if_neg nonzero]
              simp
  exact auxiliary source.clock source rfl installed valid

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.ranked_loop_current
