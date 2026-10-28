import InitECandidate.Solver.Input.LoopNormal
import InitECandidate.Solver.Input.ClockCostLoop

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real normal loop with no body break can finish only at its actual
zero test. Failed reads, invalid test types and timeouts cannot fake an exit. -/
theorem loop_normal_exit (test : ExpHOL 64) (body : ProgHOL 64)
    (noBreak : ∀ source : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState source body).1≠some .break)
    (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState source (.while test body)=(none,post)) :
    evalHOLFinite post (h:=fun address=>Classical.propDecidable (post.memaddrs address)) test=some (.val (.word 0#64)) := by
  classical
  have auxiliary : ∀ clock (current : PanSemStateFiniteExact 64 Guest.HostMemory),current.clock=clock →
      evaluateHOLFiniteState current (.while test body)=(none,post) →
      evalHOLFinite post (h:=fun address=>Classical.propDecidable (post.memaddrs address)) test=some (.val (.word 0#64)) := by
    intro clock
    induction clock using Nat.strong_induction_on with
    | h clock ih=>
      intro current clockEq normal
      rw [evaluateHOLFiniteState_while_total] at normal
      generalize read : evalHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address)) test=observed at normal
      cases observed with
      | none=>cases normal
      | some value=>
        cases value with
        | rStruct fields=>cases normal
        | nStruct name fields=>cases normal
        | val payload=>
          cases payload with
          | word word=>
            simp only at normal
            by_cases nonzero : word≠0
            · rw [if_pos nonzero] at normal
              by_cases zero : current.clock=0
              · rw [if_pos zero] at normal; cases normal
              · rw [if_neg zero] at normal
                have forward:=evaluateHOLFiniteState_clock_le (decClockHOLFinite current) body
                have safe:=noBreak (decClockHOLFinite current)
                generalize executed : evaluateHOLFiniteState (decClockHOLFinite current) body=output at normal forward safe
                obtain ⟨result,target⟩:=output
                rw [WitnessRadix.StateSteps.fixed_clock (decClockHOLFinite current) target result forward] at normal
                have earlier : target.clock<clock:=by change target.clock≤current.clock-1 at forward; omega
                cases result with
                | none=>exact ih target.clock earlier target rfl normal
                | some result=>
                  cases result with
                  | «continue»=>exact ih target.clock earlier target rfl normal
                  | «break»=>exact (safe rfl).elim
                  | returned value=>cases normal
                  | error=>cases normal
                  | timeOut=>cases normal
                  | exception identifier value=>cases normal
                  | finalFfi event=>cases normal
            · rw [if_neg nonzero] at normal
              have endpoint : current=post:=congrArg Prod.snd normal
              have zero : word=0#64:=Classical.byContradiction nonzero
              simpa only [endpoint,zero] using read
  exact auxiliary source.clock source rfl run

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.loop_normal_exit
