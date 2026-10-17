import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.MutableTable
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Canonical real call resumption for pure bodies returning tuple or scalar
values. Both declared shapes and the actual returned shape must agree. -/
theorem pure_value_call (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (function : MlS)
    (shape returnShape : ShapeHOL) (expressions : List (ExpHOL 64)) (values : List (ValueHOL 64)) (body continuation : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returned : ValueHOL 64) (paid : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some values)
    (called : lookupCodeHOLFinite source.code.lookup function values=some (body,callee,returnShape)) (enough : 1≤source.clock)
    (run : evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body=(some (.returned returned),target))
    (shapes : (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape)=true)
    (frame : emptyLocalsHOLFinite target=emptyLocalsHOLFinite {source with clock:=source.clock-1-paid}) :
    evaluateHOLFiniteState source (.decCall (ofString name) shape function expressions continuation)=
      (let output:=evaluateHOLFiniteState (setVarHOLFinite (ofString name) returned {source with clock:=source.clock-1-paid}) continuation
      (output.1,restore source name output.2)) := by
  have actual:=Input.CallNormal.return_execute source target name shape function expressions values body continuation callee returnShape returned args called enough run shapes
  have callerFrame:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with locals:=source.locals}) frame
  have canonical : Input.CallNormal.continuationEntry source target name returned=
      setVarHOLFinite (ofString name) returned {source with clock:=source.clock-1-paid} := by
    exact congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>setVarHOLFinite (ofString name) returned state) callerFrame
  rw [canonical] at actual
  exact actual

end InitECandidate.Solver.MutableTable

#print axioms InitECandidate.Solver.MutableTable.pure_value_call
