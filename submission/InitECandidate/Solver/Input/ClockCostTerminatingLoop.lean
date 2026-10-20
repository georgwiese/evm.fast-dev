import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Amortize an actual non-timeout loop by a current-state allowance.
The same observed execution derives non-timeout body and recursive runs;
no future successful return or per-iteration trace is assumed. -/
theorem potential_loop_terminating (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (allowance : PanSemStateFiniteExact 64 Guest.HostMemory → Nat)
    (step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,
      current.code=code → invariant current → ∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → current.clock≠0 →
      let output := evaluateHOLFiniteState (decClockHOLFinite current) body
      output.1≠some .timeOut → current.clock-output.2.clock≤allowance current ∧
      ((output.1=none ∨ output.1=some .continue) → invariant output.2 ∧
        current.clock-output.2.clock+allowance output.2≤allowance current))
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (codeEq : source.code=code) (valid : invariant source)
    (notTimeout : (evaluateHOLFiniteState source (.while test body)).1≠some .timeOut) :
    source.clock-(evaluateHOLFiniteState source (.while test body)).2.clock≤allowance source := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock → current.code=code → invariant current →
      (evaluateHOLFiniteState current (.while test body)).1≠some .timeOut →
      current.clock-(evaluateHOLFiniteState current (.while test body)).2.clock≤allowance current := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq installed valid notTimeout
      rw [evaluateHOLFiniteState_while_total] at notTimeout ⊢
      generalize observed : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=value at notTimeout ⊢
      cases value with
      | none => simp
      | some value =>
        cases value with
        | rStruct fields => simp
        | nStruct name fields => simp
        | val payload =>
          cases payload with
          | word word =>
            simp only at notTimeout ⊢
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at notTimeout ⊢
              by_cases zero : current.clock=0
              · rw [if_pos zero]
                simp [zero]
              · rw [if_neg zero] at notTimeout ⊢
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at bodyClock notTimeout ⊢
                obtain ⟨result,target⟩ := output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result bodyClock] at notTimeout ⊢
                have bodyNotTimeout : result≠some .timeOut := by
                  intro timed
                  subst result
                  exact notTimeout rfl
                have budget := step current installed valid word observed nonzero zero
                rw [computed] at budget
                have budget := budget bodyNotTimeout
                have stopped : current.clock-target.clock≤allowance current := budget.1
                have tail : (result=none ∨ result=some .continue) →
                    current.clock-(evaluateHOLFiniteState target (.while test body)).2.clock≤allowance current := by
                  intro continuing
                  have tailNotTimeout : (evaluateHOLFiniteState target (.while test body)).1≠some .timeOut := by
                    rcases continuing with normal | continued <;> subst result <;> exact notTimeout
                  obtain ⟨targetValid,paid⟩ := budget.2 continuing
                  change current.clock-target.clock+allowance target≤allowance current at paid
                  change target.clock≤current.clock-1 at bodyClock
                  have targetCode := (Input.evaluation_fields (decClockHOLFinite current) target body result computed).2.2.2.trans installed
                  have earlier : target.clock<clock := by change target.clock≤current.clock-1 at bodyClock; omega
                  have priced := ih target.clock earlier target rfl targetCode targetValid tailNotTimeout
                  have tailClock := evaluateHOLFiniteState_clock_le target (.while test body)
                  omega
                cases result with
                | none => exact tail (Or.inl rfl)
                | some result => cases result <;> first | exact tail (Or.inr rfl) | exact stopped
            · rw [if_neg nonzero]
              simp
  exact auxiliary source.clock source rfl codeEq valid notTimeout

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.potential_loop_terminating
