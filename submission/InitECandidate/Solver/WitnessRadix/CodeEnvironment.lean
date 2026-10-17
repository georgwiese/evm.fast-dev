import InitECandidate.Solver.WitnessRadix.Copy32Environment

namespace InitECandidate.Solver.WitnessRadix.CodeEnvironment
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact code lookup supplies a finite callee environment with exactly the
same observable lookups. No successful function execution is assumed. -/
theorem finite_lookup
    (codeFn : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (name : MlS) (values : List (ValueHOL 64)) (body : ProgHOL 64)
    (locals : MlS → Option (ValueHOL 64)) (shape : ShapeHOL)
    (raw : lookupCodeHOLExact codeFn name values = some (body, locals, shape)) :
    ∃ callee : HolFiniteMapExact MlS (ValueHOL 64),
      lookupCodeHOLFinite codeFn name values = some (body, callee, shape) ∧ callee.lookup = locals := by
  cases lookup : lookupCodeHOLFinite codeFn name values with
  | none =>
      have absent := (lookupCodeHOLFinite_eq_none_iff codeFn name values).mp lookup
      rw [raw] at absent
      cases absent
  | some data =>
      obtain ⟨body', callee, shape'⟩ := data
      have eq := lookupCodeHOLFinite_eq_some codeFn name values body' callee shape' lookup
      rw [raw] at eq
      simp only [Option.some.injEq, Prod.mk.injEq] at eq
      obtain ⟨bodyEq, localsEq, shapeEq⟩ := eq
      subst body'
      subst shape'
      exact ⟨callee, rfl, localsEq.symm⟩

end InitECandidate.Solver.WitnessRadix.CodeEnvironment

#print axioms InitECandidate.Solver.WitnessRadix.CodeEnvironment.finite_lookup
