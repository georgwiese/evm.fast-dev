import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.RlpWrite.U256Value
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A genuinely successful original unary U256 lookup supplies its actual
four-word argument, body, return shape and callee binding. -/
theorem unary_lookup (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (body : ProgHOL 64)
    (installed : code function = some ([(ofString "a", tupleShape)], body, .one))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite code function values = some (actual, callee, returnShape)) :
    ∃ words : Words, values = [tuple words] ∧ actual = body ∧ returnShape = .one ∧
      callee.lookup (ofString "a") = some (tuple words) := by
  have raw := lookupCodeHOLFinite_eq_some code function values actual callee returnShape called
  simp only [lookupCodeHOLExact, installed] at raw
  split at raw
  · rename_i valid
    have length := valid.2.1
    cases values with
    | nil => simp at length
    | cons value rest =>
      cases rest with
      | cons head tail => simp at length
      | nil =>
        have check : shapeEqHOL tupleShape (shapeOfHOLExact value) = true := by
          simpa using valid.2.2
        obtain ⟨words, valueEq⟩ := of_shape value ((shapeEqHOL_eq_true _ _).mp check).symm
        have same := Option.some.inj raw
        have bodyEq := congrArg Prod.fst same
        have shapeEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.2) same
        have cellEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "a")) same
        have cell : callee.lookup (ofString "a") = some value := by simpa using cellEq.symm
        exact ⟨words, by rw [valueEq], bodyEq.symm, shapeEq.symm, cell.trans (congrArg some valueEq)⟩
  · cases raw

end InitECandidate.Solver.Input.RlpWrite.U256Value

#print axioms InitECandidate.Solver.Input.RlpWrite.U256Value.unary_lookup
