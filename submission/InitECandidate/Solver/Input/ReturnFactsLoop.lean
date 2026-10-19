import InitECandidate.Solver.Input.ReturnFacts
import InitECandidate.Solver.Input.EvaluationFields
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input.ReturnFacts
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Carry a current invariant to the real iteration that returned a value.
Continuation preservation is required only for actual none/continue body
outcomes. No later successful iteration or whole-loop execution is assumed. -/
theorem loop (code) (test : ExpHOL 64) (body : ProgHOL 64)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory → Prop) (property : ValueHOL 64 → Prop)
    (bodyReturns : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      source.code=code → invariant source → ∀ word,
      evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → source.clock≠0 → Returns (decClockHOLFinite source) body property)
    (progress : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      source.code=code → invariant source → ∀ word,
      evalHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) test=some (.val (.word word)) →
      word≠0 → source.clock≠0 → ∀ target result,
      evaluateHOLFiniteState (decClockHOLFinite source) body=(result,target) →
      (result=none ∨ result=some .continue) → invariant target)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (installed : source.code=code) (valid : invariant source) :
    Returns source (.while test body) property := by
  classical
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock → current.code=code → invariant current → Returns current (.while test body) property := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih =>
      intro current clockEq codeEq valid post value normal
      rw [evaluateHOLFiniteState_while_total] at normal
      generalize observed : evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) test=read at normal
      cases read with
      | none => cases normal
      | some read =>
        cases read with
        | rStruct fields => cases normal
        | nStruct name fields => cases normal
        | val payload =>
          cases payload with
          | word word =>
            simp only at normal
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at normal
              by_cases zero : current.clock=0
              · rw [if_pos zero] at normal
                cases normal
              · rw [if_neg zero] at normal
                have returnedFacts := bodyReturns current codeEq valid word observed nonzero zero
                have bodyClock := evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at normal bodyClock
                obtain ⟨result,target⟩ := output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result bodyClock] at normal
                have targetCode : target.code=code := (Input.evaluation_fields (decClockHOLFinite current) target body result computed).2.2.2.trans codeEq
                have continueLoop : (result=none ∨ result=some .continue) →
                    evaluateHOLFiniteState target (.while test body)=(some (.returned value),post) → property value := by
                  intro continuing tail
                  have next := progress current codeEq valid word observed nonzero zero target result computed continuing
                  have earlier : target.clock<clock := by change target.clock≤current.clock-1 at bodyClock; omega
                  exact ih target.clock earlier target rfl targetCode next post value tail
                cases result with
                | none => exact continueLoop (Or.inl rfl) normal
                | some result =>
                  cases result with
                  | «continue» => exact continueLoop (Or.inr rfl) normal
                  | returned answer =>
                    have same := congrArg Prod.fst normal
                    have answerEq : answer=value := by simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using same
                    rw [answerEq] at computed
                    exact returnedFacts target value computed
                  | «break» => cases normal
                  | error => cases normal
                  | timeOut => cases normal
                  | exception identifier payload => cases normal
                  | finalFfi event => cases normal
            · rw [if_neg nonzero] at normal
              cases normal
  exact auxiliary source.clock source rfl installed valid

end InitECandidate.Solver.Input.ReturnFacts

#print axioms InitECandidate.Solver.Input.ReturnFacts.loop
