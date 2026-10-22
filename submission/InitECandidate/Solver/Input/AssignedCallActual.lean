import InitECandidate.Solver.Input.AssignedCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A real normally continuing assigned/ignored call derives its actual
argument values, successful lookup and genuine callee return. -/
theorem assigned_actual (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (destination : Option (VarKind×MlS)) (function : MlS) (arguments : List (ExpHOL 64))
    (normal : evaluateHOLFiniteState source (.call (some (destination,none)) function arguments)=(none,post)) :
    ∃ values body callee shape target returned,
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values ∧
      lookupCodeHOLFinite source.code.lookup function values=some (body,callee,shape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target) := by
  classical
  cases args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments with
  | none=>rw [evaluateHOLFiniteState_call,args] at normal; cases normal
  | some values=>
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none=>
      rw [evaluateHOLFiniteState_call,args] at normal
      simp only [called] at normal
      cases normal
    | some data=>
      obtain ⟨body,callee,shape⟩:=data
      obtain ⟨funded,target,returned,run⟩:=assigned_callee_return source post destination function arguments values body callee shape args called normal
      exact ⟨values,body,callee,shape,target,returned,rfl,called,run⟩

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.assigned_actual
