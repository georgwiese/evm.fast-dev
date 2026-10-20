import InitECandidate.Solver.Input.PayloadProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A passed real payload length guard exposes the original remaining body
at every clock budget, without any call or state change. -/
theorem passing_entry (entry : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (binding : entry.locals.lookup (ofString "len") = some (.val (.word word))) (minimum : 540 ≤ word.toNat) :
    evaluateHOLFiniteState entry body = evaluateHOLFiniteState entry afterGuard := by
  have test := length_test_read entry word binding
  simp only [QueryBranch.eval,if_neg (show ¬ word.toNat < 540 by omega)] at test
  have guarded : evaluateHOLFiniteState entry lengthGuard = (none,entry) := by
    rw [lengthGuard,evaluateHOLFiniteState_ite,test]
    simp
  rw [body_shape,StateSteps.next_sequence entry entry _ _ guarded (Nat.le_refl _)]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.passing_entry
