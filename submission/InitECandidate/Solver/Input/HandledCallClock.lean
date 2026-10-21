import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Once the real ignored call is funded and looked up, its exception
handler adds no source ticks when the actual handler is clock-preserving.
Every callee outcome, including mismatched/invalid exceptions, is covered. -/
theorem ignored_handled_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (function handlerId handlerVar : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body handler : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape)) (funded : source.clock≠0)
    (quiet : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,(evaluateHOLFiniteState current handler).2.clock=current.clock) :
    (evaluateHOLFiniteState source (.call (some (none,some (handlerId,handlerVar,handler))) function arguments)).2.clock=
      (evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body).2.clock := by
  classical
  rw [evaluateHOLFiniteState_call,args]
  simp only
  rw [called]
  simp only
  rw [if_neg funded]
  generalize computed : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=output
  obtain ⟨result,target⟩ := output
  cases result with
  | none=>rfl
  | some result=>
    cases result with
    | returned value=>simp only; split <;> rfl
    | exception actualId value=>
      simp only
      split
      · split
        · split
          · exact quiet _
          · rfl
        · rfl
      · rfl
    | error=>rfl
    | timeOut=>rfl
    | «break»=>rfl
    | «continue»=>rfl
    | finalFfi event=>rfl

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.ignored_handled_clock
