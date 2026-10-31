import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual loop may carry a proof index, such as its concrete linked
stack. A continuing body must produce the next index and strictly decrease
its rank. No uniqueness or arbitrary choice of a physical-state rank is needed.
Every abort/timeout/other outcome is included in the source allowance. -/
theorem ranked_loop_indexed {Index : Type} (code) (test : ExpHOL 64) (body : ProgHOL 64) (price : Nat)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Index → Prop) (rank : Index → Nat)
    (priced : ∀ (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Index),
      source.code=code → invariant source index → ∀ word : BitVec 64,
      evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → source.clock≠0 → source.clock-1-(evaluateHOLFiniteState (decClockHOLFinite source) body).2.clock≤price)
    (progress : ∀ (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Index),
      source.code=code → invariant source index → ∀ word : BitVec 64,
      evalHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → 0<rank index ∧ (source.clock≠0 →
        let output:=evaluateHOLFiniteState (decClockHOLFinite source) body
        (output.1=none ∨ output.1=some .continue) → ∃ nextIndex,invariant output.2 nextIndex ∧ rank nextIndex<rank index))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Index)
    (installed : source.code=code) (valid : invariant source index) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤(price+1)*rank index := by
  classical
  have auxiliary : ∀ clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Index),
      source.clock = clock → source.code = code → invariant source index →
      source.clock - (evaluateHOLFiniteState source (.while test body)).2.clock ≤ (price + 1) * rank index := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro source index clockEq installed valid
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
              obtain ⟨positiveRank, transition⟩ := progress source index installed valid word observed nonzero
              by_cases zero : source.clock = 0
              · rw [if_pos zero]
                simp [zero]
              · rw [if_neg zero]
                have bodyCost := priced source index installed valid word observed nonzero zero
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
                have onePrice : price + 1 ≤ (price + 1) * rank index := by
                  simpa only [Nat.mul_one] using Nat.mul_le_mul_left (price + 1) positiveRank
                have stopped : source.clock - target.clock ≤ (price + 1) * rank index := by omega
                have tail : (result = none ∨ result = some .continue) →
                    source.clock - (evaluateHOLFiniteState target (.while test body)).2.clock ≤ (price + 1) * rank index := by
                  intro continuing
                  obtain ⟨nextIndex,targetValid, smaller⟩ := transition continuing
                  change rank nextIndex < rank index at smaller
                  have earlier : target.clock < clock := by omega
                  have tailCost := ih target.clock earlier target nextIndex rfl targetCode targetValid
                  have tailClock := evaluateHOLFiniteState_clock_le target (.while test body)
                  have budget := Nat.mul_le_mul_left (price + 1) (show rank nextIndex + 1 ≤ rank index by omega)
                  rw [Nat.mul_add, Nat.mul_one] at budget
                  omega
                cases result with
                | none => exact tail (Or.inl rfl)
                | some result =>
                  cases result <;> first | exact tail (Or.inr rfl) | exact stopped
            · rw [if_neg nonzero]
              simp
  exact auxiliary source.clock source index rfl installed valid

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
  apply ranked_loop_indexed code test body price (fun current index=>index=current ∧ invariant current) rank
    (fun current index codeEq ready word read nonzero funded=>by
      obtain ⟨same,valid⟩:=ready
      subst index
      exact priced current codeEq valid word read nonzero funded)
    (fun current index codeEq ready word read nonzero=>by
      obtain ⟨same,valid⟩:=ready
      subst index
      obtain ⟨positive,transition⟩:=progress current codeEq valid word read nonzero
      refine ⟨positive,?_⟩
      intro funded
      dsimp only
      intro continuing
      obtain ⟨nextValid,smaller⟩:=transition funded continuing
      exact ⟨_,⟨rfl,nextValid⟩,smaller⟩) source source installed ⟨rfl,valid⟩

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.ranked_loop_current

#print axioms InitECandidate.Solver.Input.ClockCost.ranked_loop_indexed
