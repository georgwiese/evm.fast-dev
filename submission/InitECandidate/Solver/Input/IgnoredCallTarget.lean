import InitECandidate.Solver.Input.IgnoredCallNormal
import Guest.Model

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- An actual normal ignored call retains the real child memory/globals
and clock, and reinstalls precisely the saved caller locals. -/
theorem ignored_target (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (returned : ValueHOL 64) (target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (child : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
    (normal : evaluateHOLFiniteState source (.call (some (none,none)) function arguments)=(none,post)) :
    post={target with locals:=source.locals} := by
  have funded:=(ignored_callee_return source post function arguments values body callee shape args called normal).1
  rw [evaluateHOLFiniteState_call] at normal
  simp only [args,called,if_neg (show source.clock≠0 from by omega),child] at normal
  split at normal
  · have same:=congrArg Prod.snd normal
    exact same.symm
  · cases normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_target
