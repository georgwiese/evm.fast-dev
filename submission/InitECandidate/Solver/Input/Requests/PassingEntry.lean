import InitECandidate.Solver.Input.Requests.Entry

namespace InitECandidate.Solver.Input.Requests
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The original passing length guard consumes no source clock or effects. -/
theorem passing_entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (length : BitVec 64)
    (binding : source.locals.lookup (ofString "len") = some (.val (.word length))) (minimum : 20 ≤ length.toNat) :
    evaluateHOLFiniteState source body = evaluateHOLFiniteState source afterGuard := by
  have test := length_test_read source length binding
  simp only [if_neg (show ¬ length.toNat < 20 by omega),eval] at test
  have guarded : evaluateHOLFiniteState source shortGuard = (none,source) := by
    rw [shortGuard,evaluateHOLFiniteState_ite,test]
    simp
  rw [guard_shape,StateSteps.next_sequence source source _ _ guarded (Nat.le_refl _)]

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.passing_entry
