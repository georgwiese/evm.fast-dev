import InitECandidate.Solver.MutableTable.TableRuntime.ModelCaller
import InitECandidate.Solver.MutableTable.TableRuntime.Frames

namespace InitECandidate.Solver.MutableTable.TableRuntime
open NaturalLayout WitnessRadix

/-- Exact caller clock allowance of the checked original constructor. -/
theorem caller_price (capacity : Nat) : price capacity + 1 = if capacity = 4 then 12 else Zero.price capacity + 8 := by
  unfold price TableNew.price TableNew.clearCost
  split <;> omega

theorem rounded_of_multiple (capacity : Nat) (multiple : capacity % 8 = 0) : rounded capacity = capacity := by
  unfold rounded
  omega

/-- Exact reservation for the ordinary word-multiple capacities. -/
theorem reservation_of_multiple (kind : KeyHash.Kind) (start capacity : Nat) (multiple : capacity % 8 = 0) :
    freshEnd kind start capacity = start + 72 + (stride kind + 25) * capacity := by
  rw [reservation, rounded_of_multiple capacity multiple]
  simp only [Nat.add_mul]
  omega

end InitECandidate.Solver.MutableTable.TableRuntime

#print axioms InitECandidate.Solver.MutableTable.TableRuntime.caller_price
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.rounded_of_multiple
#print axioms InitECandidate.Solver.MutableTable.TableRuntime.reservation_of_multiple
