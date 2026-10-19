import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real ignored call with a real exception handler. Callee pricing is
derived at its current entry; the handler is priced on all actual outcomes. -/
theorem caught_current (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (handlerId handlerVar : MlS) (handler : ProgHOL 64) (price handlerPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (bodyCost : (callEntryStateHOLFinite source callee).clock-(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock≤price)
    (handlerCost : Bound source.code handler handlerPrice) :
    source.clock-(evaluateHOLFiniteState source (.call (some (none,some (handlerId,handlerVar,handler))) function arguments)).2.clock≤price+handlerPrice+1 := by
  rw [evaluateHOLFiniteState_call]
  simp only [args,called]
  by_cases zero : source.clock=0
  · rw [if_pos zero]
    change source.clock-source.clock≤_
    omega
  · rw [if_neg zero]
    have bodyClock := evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite source callee) body
    generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output at bodyCost bodyClock ⊢
    obtain ⟨result,target⟩ := output
    have cost : source.clock-target.clock≤price+handlerPrice+1 := by
      change source.clock-1-target.clock≤price at bodyCost
      change target.clock≤source.clock-1 at bodyClock
      omega
    cases result with
    | none => exact cost
    | some result =>
      cases result with
      | returned value =>
        simp only
        split <;> exact cost
      | exception exceptionId value =>
        simp only
        split
        · split
          · split
            · let ready := setVarHOLFinite handlerVar value {target with locals:=source.locals}
              have codeEq : ready.code=source.code := (Input.evaluation_fields (callEntryStateHOLFinite source callee) target body (some (.exception exceptionId value)) computed).2.2.2
              have priced := handlerCost ready codeEq
              have clock := evaluateHOLFiniteState_clock_le ready handler
              change source.clock-(evaluateHOLFiniteState ready handler).2.clock≤_
              change target.clock-(evaluateHOLFiniteState ready handler).2.clock≤handlerPrice at priced
              change (evaluateHOLFiniteState ready handler).2.clock≤target.clock at clock
              change source.clock-1-target.clock≤price at bodyCost
              change target.clock≤source.clock-1 at bodyClock
              omega
            · exact cost
          · exact cost
        · exact cost
      | error => exact cost
      | timeOut => exact cost
      | «break» => exact cost
      | «continue» => exact cost
      | finalFfi event => exact cost

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.caught_current
