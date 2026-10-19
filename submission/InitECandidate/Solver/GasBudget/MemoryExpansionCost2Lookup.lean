import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Prefix
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

/-- A successful lookup checks all four real quad arguments. -/
theorem lookup_shape (code) (installed : Input.OriginalCode.Installed code)
    (values : List (ValueHOL 64)) (actual : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
    (called : lookupCodeHOLFinite code.lookup (ofString "extend_memory_cost2") values = some (actual, callee, shape)) :
    ∃ s1 n1 s2 n2 : U256Value.Words,
      values = [U256Value.tuple s1, U256Value.tuple n1, U256Value.tuple s2, U256Value.tuple n2] := by
  have raw := lookupCodeHOLFinite_eq_some code.lookup (ofString "extend_memory_cost2") values actual callee shape called
  simp only [lookupCodeHOLExact, original_code code installed] at raw
  split at raw
  · rename_i valid
    have length := valid.2.1
    cases values with
    | nil => simp at length
    | cons a rest =>
      cases rest with
      | nil => simp at length
      | cons b rest =>
        cases rest with
        | nil => simp at length
        | cons c rest =>
          cases rest with
          | nil => simp at length
          | cons d rest =>
            cases rest with
            | cons head tail => simp at length
            | nil =>
              have checks : shapeEqHOL U256Value.tupleShape (shapeOfHOLExact a) = true ∧
                  shapeEqHOL U256Value.tupleShape (shapeOfHOLExact b) = true ∧
                  shapeEqHOL U256Value.tupleShape (shapeOfHOLExact c) = true ∧
                  shapeEqHOL U256Value.tupleShape (shapeOfHOLExact d) = true := by
                simpa using valid.2.2
              obtain ⟨s1, aEq⟩ := U256Value.of_shape a ((shapeEqHOL_eq_true _ _).mp checks.1).symm
              obtain ⟨n1, bEq⟩ := U256Value.of_shape b ((shapeEqHOL_eq_true _ _).mp checks.2.1).symm
              obtain ⟨s2, cEq⟩ := U256Value.of_shape c ((shapeEqHOL_eq_true _ _).mp checks.2.2.1).symm
              obtain ⟨n2, dEq⟩ := U256Value.of_shape d ((shapeEqHOL_eq_true _ _).mp checks.2.2.2).symm
              exact ⟨s1, n1, s2, n2, by rw [aEq, bEq, cEq, dEq]⟩
  · cases raw

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.lookup_shape
