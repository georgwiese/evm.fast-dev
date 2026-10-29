import InitECandidate.Solver.Input.PureStraight
import InitECandidate.Solver.Input.CallResume

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
variable {F : Type}

/-- A checked zero-clock straight-line body returns its actual tuple/scalar
value at an exact one-tick scoped caller prefix. -/
theorem pure_value_execute (source : PanSemStateFiniteExact 64 F)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL) (value : ValueHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,returnShape))
    (enough : 1 ≤ source.clock)
    (bodyReturns : PureStraight.Returns (callEntryStateHOLFinite source callee) body value)
    (typed : (shapeEqHOL (shapeOfHOLExact value) shape && shapeEqHOL (shapeOfHOLExact value) returnShape) = true) :
    evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) =
      let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) value {source with clock := source.clock - 1}) continuation
      (output.1,restore source name output.2) := by
  obtain ⟨target,run,frame⟩ := bodyReturns
  have actual := return_execute source target name shape function arguments values body continuation callee returnShape value args called enough run typed
  have callerFrame := congrArg (fun state : PanSemStateFiniteExact 64 F => {state with locals := source.locals}) frame
  have nextEq : continuationEntry source target name value = setVarHOLFinite (ofString name) value {source with clock := source.clock - 1} := by
    change setVarHOLFinite (ofString name) value {target with locals := source.locals} = _
    exact congrArg (fun state : PanSemStateFiniteExact 64 F => setVarHOLFinite (ofString name) value state) callerFrame
  rw [nextEq] at actual
  exact actual

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.pure_value_execute
