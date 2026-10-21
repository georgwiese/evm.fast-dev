import InitECandidate.Solver.Input.RunAttemptParentPrefix
import InitECandidate.Solver.MutableTable.WitnessBuildInputsGlobal

namespace InitECandidate.Solver.Input.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- The exact original nh/parent declarations and block-hash publications
retain caller-side inputs for either real database constructor. -/
theorem constructor_inputs (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count hashes stp pad scratch : BitVec 64) (records maximum : Nat) (slices : Nat→Graph.Slice)
    (actual : MutableTable.WitnessBuild.Inputs source array heap records maximum slices stp pad scratch) (parent : ValueHOL 64) :
    MutableTable.WitnessBuild.Inputs (constructorEntry source count hashes parent) array heap records maximum slices stp pad scratch := by
  have entered:=actual.of_fields source (parentEntry source count parent) array heap records maximum slices stp pad scratch rfl rfl rfl rfl rfl rfl
  have first:=entered.put_global (parentEntry source count parent) array heap records maximum slices stp pad scratch "block_hashes" hashes (by decide)
  exact first.put_global _ array heap records maximum slices stp pad scratch "block_hashes_n" count (by decide)

end InitECandidate.Solver.Input.RunAttempt

#print axioms InitECandidate.Solver.Input.RunAttempt.constructor_inputs
