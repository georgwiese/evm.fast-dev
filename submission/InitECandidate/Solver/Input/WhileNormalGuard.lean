import InitECandidate.Solver.Input.EvaluationFields
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine normal loop exit without a possible break/continue has
actually read a false guard in its final state. Failed reads and all stopped
body results are excluded by the observed normal execution itself. -/
theorem while_normal_guard {F : Type} (condition : ExpHOL 64) (body : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState source body).1≠some .break ∧ (evaluateHOLFiniteState source body).1≠some .continue)
    (source target : PanSemStateFiniteExact 64 F)
    (normal : evaluateHOLFiniteState source (.while condition body)=(none,target)) :
    evalHOLFinite target (h:=fun query=>Classical.propDecidable (target.memaddrs query)) condition=some (.val (.word 0#64)) := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 F),current.clock=clock→
      evaluateHOLFiniteState current (.while condition body)=(none,target)→
      evalHOLFinite target (h:=fun query=>Classical.propDecidable (target.memaddrs query)) condition=some (.val (.word 0#64)) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro current clockEq run
      rw [evaluateHOLFiniteState_while_total] at run
      generalize observed : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) condition=value at run
      cases value with
      | none=>cases run
      | some value=>
        cases value with
        | rStruct fields=>cases run
        | nStruct name fields=>cases run
        | val payload=>
          cases payload with
          | word word=>
            simp only at run
            by_cases active : word≠0
            · rw [if_pos active] at run
              by_cases zero : current.clock=0
              · rw [if_pos zero] at run; cases run
              · rw [if_neg zero] at run
                have controls:=safe (decClockHOLFinite current)
                have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at run controls forward
                obtain ⟨result,middle⟩:=output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) middle result forward] at run
                cases result with
                | none=>exact ih middle.clock (by change middle.clock≤current.clock-1 at forward; omega) middle rfl run
                | some result=>
                  cases result with
                  | «break»=>exact (controls.1 rfl).elim
                  | «continue»=>exact (controls.2 rfl).elim
                  | _=>cases run
            · rw [if_neg active] at run
              have same : target=current:=(congrArg Prod.snd run).symm
              rw [same]
              have zero : word=0#64:=Classical.not_not.mp active
              simpa only [zero] using observed
  exact auxiliary source.clock source rfl normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.while_normal_guard
