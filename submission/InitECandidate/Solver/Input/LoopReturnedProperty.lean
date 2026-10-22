import InitECandidate.Solver.Input.LoopInvariantNoControl

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Locate a genuine early loop return under an invariant maintained by
actual continuing iterations. Aborted bodies need no next-state premise. -/
theorem loop_returned_property (code) (condition : ExpHOL 64) (body : ProgHOL 64)
    (safe : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,
      (evaluateHOLFiniteState source body).1≠some .break ∧ (evaluateHOLFiniteState source body).1≠some .continue)
    (invariant : PanSemStateFiniteExact 64 Guest.HostMemory→Prop)
    (property : ValueHOL 64→PanSemStateFiniteExact 64 Guest.HostMemory→Prop)
    (step : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code→invariant current→∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word))→
      word≠0→current.clock≠0→∀ target,evaluateHOLFiniteState (decClockHOLFinite current) body=(none,target)→invariant target)
    (returned : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.code=code→invariant current→∀ word,
      evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=some (.val (.word word))→
      word≠0→current.clock≠0→∀ target value,
      evaluateHOLFiniteState (decClockHOLFinite current) body=(some (.returned value),target)→property value target)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (installed : source.code=code) (valid : invariant source)
    (normal : evaluateHOLFiniteState source (.while condition body)=(some (.returned value),target)) : property value target := by
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),
      current.clock=clock→current.code=code→invariant current→
      evaluateHOLFiniteState current (.while condition body)=(some (.returned value),target)→property value target:=by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro current clockEq codeEq valid run
      rw [evaluateHOLFiniteState_while_total] at run
      generalize observed : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) condition=actual at run
      cases actual with
      | none=>cases run
      | some actual=>
        cases actual with
        | rStruct fields=>cases run
        | nStruct name fields=>cases run
        | val payload=>
          cases payload with
          | word word=>
            simp only at run
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at run
              by_cases zero : current.clock=0
              · rw [if_pos zero] at run
                cases run
              · rw [if_neg zero] at run
                have summary:=safe (decClockHOLFinite current)
                have bodyClock:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                generalize computed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at run summary bodyClock
                obtain ⟨result,middle⟩:=output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) middle result bodyClock] at run
                cases result with
                | none=>
                  have next:=step current codeEq valid word observed nonzero zero middle computed
                  have middleCode:=(evaluation_fields (decClockHOLFinite current) middle body none computed).2.2.2.trans codeEq
                  have earlier : middle.clock<clock:=by change middle.clock≤current.clock-1 at bodyClock; omega
                  exact ih middle.clock earlier middle rfl middleCode next run
                | some result=>
                  cases result with
                  | «break»=>exact (summary.1 rfl).elim
                  | «continue»=>exact (summary.2 rfl).elim
                  | returned actualValue=>
                    have resultEq:=congrArg Prod.fst run
                    have valueEq : actualValue=value:=by
                      simpa only [Option.some.injEq,PanSemResultExact.returned.injEq] using resultEq
                    have targetEq : middle=target:=congrArg Prod.snd run
                    subst actualValue
                    subst target
                    exact returned current codeEq valid word observed nonzero zero middle value computed
                  | error=>cases run
                  | timeOut=>cases run
                  | exception identifier payload=>cases run
                  | finalFfi event=>cases run
            · rw [if_neg nonzero] at run
              cases run
  exact auxiliary source.clock source rfl installed valid normal

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.loop_returned_property
