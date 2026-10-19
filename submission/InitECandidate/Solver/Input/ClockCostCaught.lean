import InitECandidate.Solver.Input.ClockCostCaughtAssigned

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
    source.clock-(evaluateHOLFiniteState source (.call (some (none,some (handlerId,handlerVar,handler))) function arguments)).2.clock≤price+handlerPrice+1 :=
  caught_destination_current source none function arguments values body callee shape handlerId handlerVar handler price handlerPrice
    args called bodyCost handlerCost

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.caught_current
