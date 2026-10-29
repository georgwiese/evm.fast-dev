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

/-- Identify the true callee of a reached scoped action from its actual
arguments and current code, retaining the exact saved-caller restoration. -/
theorem Reaches.scoped_known {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (name : MlS) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (values : List (ValueHOL 64)) (program : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expected : lookupCodeHOLFinite source.code.lookup function values=some (program,callee,returnShape))
    (reached : Reaches source (.scoped name shape function arguments) target) :
    ∃ child returned,evaluateHOLFiniteState (callEntryStateHOLFinite source callee) program=(some (.returned returned),child) ∧
      target=setVarHOLFinite name returned {child with locals:=source.locals} := by
  cases reached with
  | «scoped» _ _ _ _ actualValues actualProgram actualCallee actualShape returned child args called funded run checked=>
    have sameValues : actualValues=values:=Option.some.inj (args.symm.trans argsRead)
    subst actualValues
    have same:=Option.some.inj (called.symm.trans expected)
    have bodyEq:=congrArg Prod.fst same
    have calleeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) same
    have shapeEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.2) same
    change actualProgram=program at bodyEq
    change actualCallee=callee at calleeEq
    change actualShape=returnShape at shapeEq
    subst actualProgram
    subst actualCallee
    subst actualShape
    exact ⟨child,returned,run,rfl⟩

end InitECandidate.Solver.Input.CallPrefix

#print axioms InitECandidate.Solver.Input.CallPrefix.Execution.head
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.scoped_actual
#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.scoped_funded

#print axioms InitECandidate.Solver.Input.CallPrefix.Reaches.scoped_known
