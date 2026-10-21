import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CallArguments
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Same actual argument values give the same original ordinary-call
execution, including failures, clock and full state. This only relates
expression reifications; it changes neither caller nor callee code. -/
theorem equivalent {F : Type} (source : PanSemStateFiniteExact 64 F) (info) (function : MlS) (arguments replacement : List (ExpHOL 64))
    (same : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) replacement) :
    evaluateHOLFiniteState source (.call info function arguments)=evaluateHOLFiniteState source (.call info function replacement) := by
  classical
  rw [evaluateHOLFiniteState_call,evaluateHOLFiniteState_call,same]

end InitECandidate.Solver.Input.CallArguments

#print axioms InitECandidate.Solver.Input.CallArguments.equivalent
