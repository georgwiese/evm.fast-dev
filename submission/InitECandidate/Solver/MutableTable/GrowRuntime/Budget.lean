import InitECandidate.Solver.MutableTable.GrowRuntime.Loop
import InitECandidate.Solver.MutableTable.GrowRuntime.Stores
import InitECandidate.Solver.MutableTable.WitnessBuildBudget

namespace InitECandidate.Solver.MutableTable.GrowRuntime

/-- Exact arithmetic sum of the checked rehash-loop allowances. -/
theorem loop_price_formula (kind : KeyHash.Kind) (cursor remaining : Nat) :
    loopPrice kind cursor remaining = remaining * cursor + WitnessBuild.triangle remaining +
      remaining * (KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 3) := by
  induction remaining generalizing cursor with
  | zero => simp [loopPrice, WitnessBuild.triangle]
  | succ remaining ih =>
    simp only [loopPrice, ih, WitnessBuild.triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega

/-- From an empty new table, all five key widths have a quadratic collision
term plus their actual hash/copy and loop caller allowances. These are source
clocks; compiler/target and whole-program event counts remain separate. -/
theorem empty_loop_price (kind : KeyHash.Kind) (count : Nat) : loopPrice kind 0 count = WitnessBuild.triangle count +
    count * (match kind with | .account => 10 | .indexedAccount => 18 | .word => 8 | .storage => 14 | .indexedStorage => 26) := by
  rw [loop_price_formula]
  cases kind <;> simp [KeyHash.hashPrice, KeyHash.keySize, MemeqByteRuntime.price]

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.loop_price_formula
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.empty_loop_price
