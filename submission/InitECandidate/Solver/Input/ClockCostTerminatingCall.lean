import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.ClockCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open LocalEffects (callInfo)

/-- Transfer a callee bound for observed non-timeout executions through
an actual ordinary call. Errors, escaping exceptions and FFI outcomes are
included; no successful return is assumed. -/
theorem call_current_terminating (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (Option MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL) (price : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape))
    (bodyCost : ∀ result target,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(result,target) → result≠some .timeOut →
      (callEntryStateHOLFinite source callee).clock-target.clock≤price)
    (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source (.call (callInfo destination) function arguments)=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤price+1 := by
  have positive : source.clock≠0 := by
    intro zero
    have actual:=run
    rw [evaluateHOLFiniteState_call,args] at actual
    simp only [called,if_pos zero] at actual
    exact notTimeout (congrArg Prod.fst actual).symm
  have calleeNotTimeout : (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1≠some .timeOut := by
    intro timed
    have timedRun : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=
        (some .timeOut,(evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2) := Prod.ext timed rfl
    have actual:=run
    rw [evaluateHOLFiniteState_call,args] at actual
    simp only [called,if_neg positive] at actual
    rw [timedRun] at actual
    cases destination <;> simp only [callInfo,Option.map_none,Option.map_some] at actual
    all_goals exact notTimeout (congrArg Prod.fst actual).symm
  have cost := bodyCost (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).1
    (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2 rfl calleeNotTimeout
  have caller := call_current source destination function arguments values body callee shape price args called cost
  rw [run] at caller
  exact caller

end InitECandidate.Solver.Input.ClockCost

#print axioms InitECandidate.Solver.Input.ClockCost.call_current_terminating
