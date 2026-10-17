import InitECandidate.Solver.MutableTable.PureValueCall

namespace InitECandidate.Solver.MutableTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Canonical actual declared-call resumption for a body that changes owned
memory, pays its clocks and preserves all other nonlocal state. -/
theorem memory_value_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (function : MlS)
    (shape returnShape : ShapeHOL) (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body continuation : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returned : ValueHOL 64) (paid : Nat) (memory : WitnessRadix.WordWrites.Memory)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
    (shapes : (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-paid}) :
    evaluateHOLFiniteState source (.decCall (ofString name) shape function expressions continuation)=
      (let output:=evaluateHOLFiniteState
        (setVarHOLFinite (ofString name) returned {source with memory:=memory,clock:=source.clock-1-paid}) continuation
      (output.1,restore source name output.2)) := by
  have actual:=Input.CallNormal.return_execute source target name shape function expressions values body continuation callee returnShape returned args called enough run shapes
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have canonical : Input.CallNormal.continuationEntry source target name returned=
      setVarHOLFinite (ofString name) returned {source with memory:=memory,clock:=source.clock-1-paid} := by
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) returned state) callerFrame
  rw [canonical] at actual
  exact actual

/-- Exact ignored-result caller for memory-changing helper bodies. -/
theorem ignored_memory_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (function : MlS)
    (returnShape : ShapeHOL) (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returned : ValueHOL 64) (paid : Nat) (memory : WitnessRadix.WordWrites.Memory)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
    (shape : shapeEqHOL (shapeOfHOLExact returned) returnShape=true)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with memory:=memory,clock:=source.clock-1-paid}) :
    evaluateHOLFiniteState source (.call (some (none,none)) function expressions)=
      (none,{source with memory:=memory,clock:=source.clock-1-paid}) := by
  have actual:=evaluateHOLFiniteState_call_return_caller_locals source none function expressions values body callee returnShape returned target
    args called (by omega) run shape
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  exact actual.trans (congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>(none,state)) callerFrame)

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.memory_value_call
#print axioms InitECandidate.Solver.MutableTable.ignored_memory_call
