import InitECandidate.Solver.MutableTable.DeleteModelCall

namespace InitECandidate.Solver.MutableTable.Delete

/-- Caller prices include real lookup, all occupied deletion hash/copy
iterations, the final empty while step and the outer caller clock. -/
theorem model_caller_price (kind : KeyHash.Kind) (count : Nat) :
    modelPrice kind count + 1 = match kind with
      | .account => 8 * count + 9 * (count - 1) + 4
      | .indexedAccount => 9 * count + 17 * (count - 1) + 11
      | .word => 6 * count + 7 * (count - 1) + 4
      | .storage => 12 * count + 13 * (count - 1) + 4
      | .indexedStorage => 13 * count + 25 * (count - 1) + 15 := by
  cases kind <;> dsimp only [modelPrice, Insert.findPrice, Find.generalProbePrice, tailPrice, scanPrice,
    KeyHash.hashPrice, KeyHash.keySize, MemeqByteRuntime.price] <;> omega

theorem model_caller_positive_price (kind : KeyHash.Kind) (count : Nat) (positive : 0 < count) :
    modelPrice kind count + 1 = match kind with
      | .account => 17 * count - 5
      | .indexedAccount => 26 * count - 6
      | .word => 13 * count - 3
      | .storage => 25 * count - 9
      | .indexedStorage => 38 * count - 10 := by
  rw [model_caller_price]
  cases kind <;> dsimp only <;> omega

end InitECandidate.Solver.MutableTable.Delete

#print axioms InitECandidate.Solver.MutableTable.Delete.model_caller_price
#print axioms InitECandidate.Solver.MutableTable.Delete.model_caller_positive_price
