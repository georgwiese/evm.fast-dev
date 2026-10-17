import InitECandidate.Solver.MutableTable.SetNoGrowthCall

namespace InitECandidate.Solver.MutableTable.Set

/-- Explicit caller source-clock allowances. The updater-only case is faster;
the common allowance also includes an actual absent-key insertion. -/
theorem no_growth_caller_price (kind : KeyHash.Kind) (count : Nat) : noGrowthPrice kind count + 1 =
    match kind with
    | .account => 9 * count + 12
    | .indexedAccount => 10 * count + 27
    | .word => 7 * count + 10
    | .storage => 13 * count + 16
    | .indexedStorage => 14 * count + 39 := by
  cases kind <;> simp [noGrowthPrice, Insert.findPrice, Insert.rawPrice, Find.generalProbePrice,
    KeyHash.hashPrice, KeyHash.keySize, MemeqByteRuntime.price] <;> omega

/-- The actual no-growth occupancy condition also excludes item-count word
wrap on the insertion path. Ownership/reachability must supply the condition. -/
theorem no_growth_count_nowrap (bits count covering : Nat) (small : bits < 64)
    (countBound : count ≤ covering) (room : 2 * covering + 2 ≤ 2 ^ bits) : count + 1 < 2 ^ 64 := by
  have high := Nat.pow_lt_pow_right (by decide : 1 < (2 : Nat)) small
  omega

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.no_growth_caller_price
#print axioms InitECandidate.Solver.MutableTable.Set.no_growth_count_nowrap
