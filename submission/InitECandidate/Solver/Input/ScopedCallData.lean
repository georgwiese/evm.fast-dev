import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A real normal scoped call derives argument/code lookup, funding, the
genuine callee return and checked shapes, followed by its actual continuation.
Useful when opcode argument values come from earlier actual stack pops. -/
theorem scoped_data (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : String) (shape : ShapeHOL) (function : MlS) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape function arguments continuation) = (some (.returned value), post)) :
    1 ≤ source.clock ∧ ∃ values body callee returnShape target returned inner,
      evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some values ∧
      lookupCodeHOLFinite source.code.lookup function values = some (body, callee, returnShape) ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite source callee) body = (some (.returned returned), target) ∧
      (shapeEqHOL (shapeOfHOLExact returned) shape && shapeEqHOL (shapeOfHOLExact returned) returnShape) = true ∧
      evaluateHOLFiniteState (continuationEntry source target name returned) continuation = (some (.returned value), inner) ∧
      post = restore source name inner := by
  classical
  have expanded := normal
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at expanded
  cases args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments with
  | none => simp only [args] at expanded; cases expanded
  | some values =>
    simp only [args] at expanded
    cases called : lookupCodeHOLFinite source.code.lookup function values with
    | none => simp only [called] at expanded; cases expanded
    | some data =>
      obtain ⟨body, callee, returnShape⟩ := data
      obtain ⟨positive, target, returned, inner, bodyRun, checked, continuationRun, postEq⟩ :=
        scoped_normal source post name shape function arguments values body continuation callee returnShape args called value normal
      exact ⟨positive, values, body, callee, returnShape, target, returned, inner, rfl, called, bodyRun, checked, continuationRun, postEq⟩

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scoped_data
