import InitECandidate.Solver.Input.ClockCostCaughtAssigned
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Observe the actual child of a caught assigned call before assigning
its body a bound. Genuine handler/footer spending is retained as a finite
overhead, including failed exception-shape checks and early child outcomes. -/
theorem caught_sequence_observe (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (VarKind×MlS)) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body footer : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (identifier parameter : MlS) (handler : ProgHOL 64) (handlerPrice footerPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (handlerCost : ClockCost.Bound source.code handler handlerPrice) (footerCost : ClockCost.Bound source.code footer footerPrice)
    (outcome : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.seq (.call (some (destination,some (identifier,parameter,handler))) function arguments) footer)=(outcome,post)) :
    source.clock-post.clock≤1 ∨ ∃ target childResult,
      1≤source.clock ∧ evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(childResult,target) ∧
      source.clock-post.clock≤(callEntryStateHOLFinite source callee).clock-target.clock+handlerPrice+footerPrice+1 := by
  by_cases zero : source.clock=0
  · exact Or.inl (by omega)
  · let entry:=callEntryStateHOLFinite source callee
    let output:=evaluateHOLFiniteState entry body
    have priced : entry.clock-(evaluateHOLFiniteState entry body).2.clock≤entry.clock-output.2.clock := Nat.le_refl _
    have callPrice:=ClockCost.caught_destination_current source destination function arguments values body callee shape identifier parameter handler
      (entry.clock-output.2.clock) handlerPrice args called priced handlerCost
    have full:=ClockCost.sequence_current source (.call (some (destination,some (identifier,parameter,handler))) function arguments) footer
      (entry.clock-output.2.clock+handlerPrice+1) footerPrice callPrice footerCost
    rw [run] at full
    change source.clock-post.clock≤entry.clock-output.2.clock+handlerPrice+1+footerPrice at full
    refine Or.inr ⟨output.2,output.1,by omega,rfl,?_⟩
    change source.clock-post.clock≤entry.clock-output.2.clock+handlerPrice+footerPrice+1
    omega

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.caught_sequence_observe
