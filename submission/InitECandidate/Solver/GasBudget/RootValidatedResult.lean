import InitECandidate.Solver.GasBudget.RootValidationNormal
import Mathlib.Data.List.Basic

namespace InitECandidate.Solver.GasBudget.RootValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

private theorem word_of_shape (value : ValueHOL 64) (shape : shapeOfHOLExact value = .one) :
    ∃ word : BitVec 64, value = .val (.word word) := by
  cases value with
  | val payload => cases payload with | word word => exact ⟨word, rfl⟩
  | rStruct fields => simp [shapeOfHOLExact] at shape
  | nStruct name fields => simp [shapeOfHOLExact] at shape

theorem triple_of_shape (value : ValueHOL 64)
    (shape : shapeEqHOL (shapeOfHOLExact value) intrinsicShape = true) :
    ∃ regular state floor : BitVec 64, value = RootBudget.intrinsicValue regular state floor := by
  have equal := (shapeEqHOL_eq_true _ _).mp shape
  cases value with
  | val payload => simp [shapeOfHOLExact, intrinsicShape] at equal
  | nStruct name fields => simp [shapeOfHOLExact, intrinsicShape] at equal
  | rStruct fields =>
    simp only [shapeOfHOLExact, intrinsicShape, ShapeHOL.comb.injEq] at equal
    have maps : fields.map shapeOfHOLExact = [.one, .one, .one] := equal
    have lengths := congrArg List.length maps
    have count : fields.length = 3 := by simpa using lengths
    obtain ⟨first, second, third, rfl⟩ := List.length_eq_three.mp count
    have each : shapeOfHOLExact first = .one ∧ shapeOfHOLExact second = .one ∧ shapeOfHOLExact third = .one := by
      simpa using maps
    obtain ⟨regular, rfl⟩ := word_of_shape first each.1
    obtain ⟨state, rfl⟩ := word_of_shape second each.2.1
    obtain ⟨floor, rfl⟩ := word_of_shape third each.2.2
    exact ⟨regular, state, floor, rfl⟩

/-- The entire unchanged validator returns an actual triple with both caps,
without assuming the intrinsic routine's result or successful intermediate reads. -/
theorem normal_result (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (shape : source.eshapes.lookup (Flapjack.Basis.Pure.MlString.ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ regular state floor : BitVec 64,
      returned = RootBudget.intrinsicValue regular state floor ∧
      regular.toNat ≤ 16777216 ∧ floor.toNat ≤ 16777216 := by
  obtain ⟨r, f, first, third, rBound, fBound, typed⟩ := normal_caps source post returned shape run
  obtain ⟨regular, state, floor, returnedEq⟩ := triple_of_shape returned typed
  rw [returnedEq] at first third
  have regularEq : regular = r := by simpa [fieldValue, RootBudget.intrinsicValue] using first
  have floorEq : floor = f := by simpa [fieldValue, RootBudget.intrinsicValue] using third
  refine ⟨regular, state, floor, returnedEq, ?_, ?_⟩
  · rw [regularEq]
    exact rBound
  · rw [floorEq]
    exact fBound

/-- The real validator's result supplies the cap needed by the checked
transaction-root min split, even if the total/state reservoir is much larger. -/
theorem validated_liquid (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (returned : ValueHOL 64)
    (shape : source.eshapes.lookup (Flapjack.Basis.Pure.MlString.ofString "TxErr") = some .one)
    (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ regular state floor : BitVec 64, returned = RootBudget.intrinsicValue regular state floor ∧
      floor.toNat ≤ 16777216 ∧ ∀ gas intrinsic : BitVec 64,
        (RootBudget.liquidWord gas intrinsic regular).toNat + regular.toNat ≤ 16777216 := by
  obtain ⟨regular, state, floor, valueEq, regularCap, floorCap⟩ := normal_result source post returned shape run
  exact ⟨regular, state, floor, valueEq, floorCap, fun gas intrinsic => RootBudget.liquid_bound gas intrinsic regular regularCap⟩

end InitECandidate.Solver.GasBudget.RootValidation

#print axioms InitECandidate.Solver.GasBudget.RootValidation.triple_of_shape
#print axioms InitECandidate.Solver.GasBudget.RootValidation.normal_result
#print axioms InitECandidate.Solver.GasBudget.RootValidation.validated_liquid
