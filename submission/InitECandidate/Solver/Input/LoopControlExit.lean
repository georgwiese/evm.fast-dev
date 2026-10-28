import InitECandidate.Solver.Input.EvaluationFields
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuine normal loop exit either has its actual zero guard or comes
from a real body break. Continuing bodies alone must establish the next
invariant; errors, returns and timeouts cannot supply an exit state. -/
theorem loop_control_exit (test : ExpHOL 64) (body : ProgHOL 64)
    (invariant finished : PanSemStateFiniteExact 64 Guest.HostMemory → Prop)
    (done : ∀ current,invariant current →
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word 0#64)) → finished current)
    (progress : ∀ current,invariant current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) →
      word≠0#64 → current.clock≠0 → ∀ target result,evaluateHOLFiniteState (decClockHOLFinite current) body=(result,target) →
      (result=none ∨ result=some .continue) → invariant target)
    (breaks : ∀ current,invariant current → ∀ word,
      evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=some (.val (.word word)) →
      word≠0#64 → current.clock≠0 → ∀ target,evaluateHOLFiniteState (decClockHOLFinite current) body=(some .break,target) → finished target)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ready : invariant source)
    (normal : evaluateHOLFiniteState source (.while test body)=(none,post)) : finished post := by
  classical
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),current.clock=clock → invariant current →
      evaluateHOLFiniteState current (.while test body)=(none,post) → finished post := by
    intro clock
    induction clock using Nat.strongRecOn with
    | ind clock ih=>
      intro current clockEq state run
      rw [evaluateHOLFiniteState_while_total] at run
      generalize observed : evalHOLFinite current (h:=fun query=>Classical.propDecidable (current.memaddrs query)) test=read at run
      cases read with
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
              · rw [if_pos zero] at run
                cases run
              · rw [if_neg zero] at run
                have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize executed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at run forward
                obtain ⟨result,target⟩:=output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result forward] at run
                have earlier : target.clock<clock := by change target.clock≤current.clock-1 at forward; omega
                cases result with
                | none=>exact ih target.clock earlier target rfl (progress current state word observed active zero target none executed (Or.inl rfl)) run
                | some result=>
                  cases result with
                  | «continue»=>exact ih target.clock earlier target rfl (progress current state word observed active zero target (some .continue) executed (Or.inr rfl)) run
                  | «break»=>
                    have endpoint:=congrArg Prod.snd run
                    dsimp only at endpoint
                    rw [←endpoint]
                    exact breaks current state word observed active zero target executed
                  | returned value=>cases run
                  | error=>cases run
                  | timeOut=>cases run
                  | exception name value=>cases run
                  | finalFfi event=>cases run
            · rw [if_neg active] at run
              have endpoint:=congrArg Prod.snd run
              dsimp only at endpoint
              have zero : word=0#64 := Classical.byContradiction active
              rw [←endpoint]
              exact done current state (by simpa only [zero] using observed)
  exact auxiliary source.clock source rfl ready normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.loop_control_exit
