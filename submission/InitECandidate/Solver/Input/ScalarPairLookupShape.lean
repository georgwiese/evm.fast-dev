import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.Input.CallNormal
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful actual two-scalar lookup derives its real argument words
and both callee bindings. No successful argument read is an input premise. -/
theorem scalar_pair_lookup_shape (code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (function : MlS) (body : ProgHOL 64) (expectedShape : ShapeHOL)
    (installed : code function = some ([(ofString "a", .one), (ofString "b", .one)], body, expectedShape))
    (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (called : lookupCodeHOLFinite code function values = some (actual, callee, returnShape)) :
    ∃ a b : BitVec 64, values = [.val (.word a), .val (.word b)] ∧ actual = body ∧ returnShape = expectedShape ∧
      callee.lookup (ofString "a") = some (.val (.word a)) ∧ callee.lookup (ofString "b") = some (.val (.word b)) := by
  have raw := lookupCodeHOLFinite_eq_some code function values actual callee returnShape called
  simp only [lookupCodeHOLExact, installed] at raw
  split at raw
  · rename_i valid
    have length := valid.2.1
    cases values with
    | nil => simp at length
    | cons left rest =>
      cases rest with
      | nil => simp at length
      | cons right rest =>
        cases rest with
        | cons head tail => simp at length
        | nil =>
          have checks : shapeEqHOL .one (shapeOfHOLExact left) = true ∧ shapeEqHOL .one (shapeOfHOLExact right) = true := by
            simpa using valid.2.2
          obtain ⟨a, leftEq⟩ := RlpWrite.U256Value.scalar_word left ((shapeEqHOL_eq_true _ _).mp checks.1).symm
          obtain ⟨b, rightEq⟩ := RlpWrite.U256Value.scalar_word right ((shapeEqHOL_eq_true _ _).mp checks.2).symm
          have same := Option.some.inj raw
          have bodyEq := congrArg Prod.fst same
          have shapeEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.2) same
          have aEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "a")) same
          have bEq := congrArg (fun triple : ProgHOL 64 × (MlS → Option (ValueHOL 64)) × ShapeHOL => triple.2.1 (ofString "b")) same
          have aCell : callee.lookup (ofString "a") = some left := by
            simpa [show ofString "a" ≠ ofString "b" from by decide] using aEq.symm
          have bCell : callee.lookup (ofString "b") = some right := by simpa using bEq.symm
          exact ⟨a, b, by rw [leftEq, rightEq], bodyEq.symm, shapeEq.symm,
            aCell.trans (congrArg some leftEq), bCell.trans (congrArg some rightEq)⟩
  · cases raw

end InitECandidate.Solver.Input.CallNormal

#print axioms InitECandidate.Solver.Input.CallNormal.scalar_pair_lookup_shape
