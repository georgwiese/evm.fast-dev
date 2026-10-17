import InitECandidate.Solver.MutableTable.GrowRuntime.Call
import InitECandidate.Solver.MutableTable.GrowRuntime.Budget

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open NaturalLayout WitnessRadix

/-- Explicit complete caller allowance: all five allocations, actual clear,
every rehash iteration, return, scopes and ignored-result call. -/
theorem caller_price (kind : KeyHash.Kind) (capacity count : Nat) :
    price kind (2 * capacity) count + 1 = Zero.price (2 * capacity) + WitnessBuild.triangle count +
      count * (match kind with | .account => 10 | .indexedAccount => 18 | .word => 8 | .storage => 14 | .indexedStorage => 26) + 7 := by
  rw [price, empty_loop_price]
  cases kind <;> dsimp only [setupPrice] <;> omega

/-- Growth allocates five arrays and reuses the existing header. This is
exact reserved space, including rounding of the original used-byte array. -/
theorem reservation (kind : KeyHash.Kind) (start capacity : Nat) :
    relocatedEnd kind start capacity - start = (stride kind + 24) * capacity + rounded capacity := by
  dsimp only [relocatedEnd]
  simp only [Nat.add_mul]
  omega

theorem reservation_multiple (kind : KeyHash.Kind) (start capacity : Nat) (multiple : capacity % 8 = 0) :
    relocatedEnd kind start capacity - start = (stride kind + 25) * capacity := by
  have roundedEq : rounded capacity = capacity := by
    have bounds := rounded_bounds capacity
    omega
  rw [reservation, roundedEq]
  simp only [Nat.add_mul]
  omega

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.caller_price
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reservation
#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.reservation_multiple
