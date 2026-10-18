import InitECandidate.Solver.GasBudget.SaturatingAdd
import InitECandidate.Solver.GasBudget.FrameSums

namespace InitECandidate.Solver.GasBudget.ForwardCredit
open Flapjack

/-- Original CALL/CALLCODE transfer surcharge uses the same value-zero
test as the forwarded-gas stipend. -/
def valueFee (words : U256Zero.Quad) : BitVec 64 :=
  if U256Zero.resultWord words = 0#64 then 11300#64 else 0#64

/-- The original saturated first charge funds the stipend and leaves at
least100 net used credit, even when memory cost saturates. This is arithmetic
over the original operands; their actual opcode reachability remains open. -/
theorem surplus (words : U256Zero.Quad) (access memoryCost : BitVec 64)
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000) :
    (CallGas.stipend words).toNat + 100 ≤ (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat := by
  have lower := SaturatingAdd.ge_left (access + valueFee words) memoryCost
  change (access + valueFee words).toNat ≤ (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat at lower
  by_cases nonzero : U256Zero.resultWord words = 0#64
  · simp only [valueFee, CallGas.stipend, if_pos nonzero] at lower ⊢
    have number : (access + 11300#64).toNat = access.toNat + 11300 := by
      rw [BitVec.toNat_add_of_lt (by change access.toNat + 11300 < 2^64; omega)]
      rfl
    rw [number] at lower
    change 2300 + 100 ≤ _
    omega
  · simp only [valueFee, CallGas.stipend, if_neg nonzero, BitVec.add_zero] at lower ⊢
    change 0 + 100 ≤ _
    omega

/-- Net progress for a real physical used-sum debit once an actual first
charge and its stipend transfer have both been accounted for. -/
theorem used_sum_progress (before current after : Memory) (frames : List (BitVec 64))
    (words : U256Zero.Quad) (access memoryCost : BitVec 64)
    (accessLower : 100 ≤ access.toNat) (accessUpper : access.toNat ≤ 3000)
    (credited : FrameSums.used before frames + (SaturatingAdd.resultWord (access + valueFee words) memoryCost).toNat ≤ FrameSums.used current frames)
    (transferred : FrameSums.used after frames + (CallGas.stipend words).toNat = FrameSums.used current frames) :
    FrameSums.used before frames + 100 ≤ FrameSums.used after frames := by
  have funded := surplus words access memoryCost accessLower accessUpper
  omega

end InitECandidate.Solver.GasBudget.ForwardCredit

#print axioms InitECandidate.Solver.GasBudget.ForwardCredit.surplus
#print axioms InitECandidate.Solver.GasBudget.ForwardCredit.used_sum_progress
