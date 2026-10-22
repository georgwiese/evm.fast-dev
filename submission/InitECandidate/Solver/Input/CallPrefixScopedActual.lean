import InitECandidate.Solver.Input.CallPrefixExecution

namespace InitECandidate.Solver.Input.CallPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem Execution.head {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {action : Action} {rest : List Action}
    (execution : Execution source (action::rest) target) :
    ∃ middle,Reaches source action middle ∧ Execution middle rest target := by
  cases execution with
  | step first next=>exact ⟨_,first,next⟩

/-- Expose the true checked scoped helper invocation, retaining its real
argument read, lookup and callee return rather than supplying them. -/
theorem Reaches.scoped_actual {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {shape : ShapeHOL} {function : MlS} {arguments : List (ExpHOL 64)}
    (reached : Reaches source (.scoped name shape function arguments) target) :
    ∃ values body callee returnShape returned childTarget,
      evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some values ∧
      lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),childTarget) := by
  cases reached with
  | «scoped» _ _ _ _ values body callee returnShape returned childTarget args called funded run checked=>
    exact ⟨values,body,callee,returnShape,returned,childTarget,args,called,run⟩

theorem Reaches.scoped_funded {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {name : MlS} {shape : ShapeHOL} {function : MlS} {arguments : List (ExpHOL 64)}
    (reached : Reaches source (.scoped name shape function arguments) target) : source.clock≠0 := by
  cases reached with
  | «scoped» _ _ _ _ values body callee returnShape returned childTarget args called funded run checked=>exact funded

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.head
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.scoped_actual
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.scoped_funded
