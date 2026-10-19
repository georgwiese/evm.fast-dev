import InitECandidate.Solver.Input.UnaryCallData

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Actual successful binary lookup retains both known argument values,
with arbitrary argument and result shapes. -/
theorem binary_lookup_known (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function leftName rightName : MlS) (leftShape rightShape : ShapeHOL) (body : ProgHOL 64) (expectedShape : ShapeHOL)
    (left right : ValueHOL 64) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (distinct : leftName ≠ rightName)
    (installed : code function = some ([(leftName, leftShape), (rightName, rightShape)], body, expectedShape))
    (called : lookupCodeHOLFinite code function [left, right] = some (actual, callee, returnShape)) :
    actual = body ∧ returnShape = expectedShape ∧ callee.lookup leftName = some left ∧ callee.lookup rightName = some right := by
  have raw := lookupCodeHOLFinite_eq_some code function [left, right] actual callee returnShape called
  simp only [lookupCodeHOLExact, installed] at raw
  split at raw
  · have same := Option.some.inj raw
    have bodyEq := congrArg Prod.fst same
    have shapeEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.2) same
    have leftEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 leftName) same
    have rightEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 rightName) same
    exact ⟨bodyEq.symm, shapeEq.symm, by simpa [distinct] using leftEq.symm, by simpa using rightEq.symm⟩
  · cases raw

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.binary_lookup_known
