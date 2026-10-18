import InitECandidate.Solver.Input.PureReturn

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A genuinely successful unary code lookup derives the one actual value,
its checked formal shape and its real callee binding. The value can be a
tuple; no successful argument/shape check is assumed separately. -/
theorem unary_lookup_data
    (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function parameter : MlS) (formalShape : ShapeHOL) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (entry : codeFn function = some ([(parameter, formalShape)], body, returnShape))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (actualShape : ShapeHOL)
    (lookedUp : lookupCodeHOLFinite codeFn function values = some (actual, callee, actualShape)) :
    ∃ value, values = [value] ∧ actual = body ∧ actualShape = returnShape ∧
      shapeOfHOLExact value = formalShape ∧ callee.lookup parameter = some value := by
  have raw := lookupCodeHOLFinite_eq_some codeFn function values actual callee actualShape lookedUp
  simp only [lookupCodeHOLExact, entry] at raw
  split at raw
  · rename_i valid
    have length := valid.2.1
    cases values with
    | nil => simp at length
    | cons value rest =>
      have restNil : rest = [] := by
        cases rest with
        | nil => rfl
        | cons head tail => simp at length
      subst rest
      have typed : shapeEqHOL formalShape (shapeOfHOLExact value) = true := by simpa using valid.2.2
      have shapeEq : shapeOfHOLExact value = formalShape := by
        have equal : formalShape = shapeOfHOLExact value := by simpa only [shapeEqHOL_eq_true] using typed
        exact equal.symm
      simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_left, List.foldl_cons, List.foldl_nil] at raw
      have pairEq := Option.some.inj raw
      have bodyEq := congrArg Prod.fst pairEq
      have shapeResult := congrArg (fun data => data.2.2) pairEq
      have binding := congrArg (fun data => data.2.1 parameter) pairEq
      refine ⟨value, rfl, bodyEq.symm, shapeResult.symm, shapeEq, ?_⟩
      simpa using binding.symm
  · cases raw

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.unary_lookup_data
