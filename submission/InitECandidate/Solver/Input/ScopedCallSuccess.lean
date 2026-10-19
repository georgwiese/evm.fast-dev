import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_success (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64))
    (body continuation : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values)
    (called : lookupCodeHOLFinite source.code.lookup function values = some (body,callee,returnShape))
    (result : Option (PanSemResultExact 64)) (success : result = none ∨ ∃ value, result = some (.returned value))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (result,post)) :
    1 ≤ source.clock ∧ ∃ target returned inner,
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned),target) ∧
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape) = true ∧
      evaluateHOLFiniteState (continuationEntry source target name returned) continuation = (result,inner) ∧
      post = restore source name inner := by
  rcases success with same | ⟨value,same⟩
  · subst result
    exact scoped_none source post name shape function arguments values body continuation callee returnShape args called normal
  · subst result
    exact scoped_normal source post name shape function arguments values body continuation callee returnShape args called value normal

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_success
