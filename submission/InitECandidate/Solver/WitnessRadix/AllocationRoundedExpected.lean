import InitECandidate.Solver.WitnessRadix.AllocationArithmetic

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc

theorem rounded_expected (pointer amount : BitVec 64) (next : Nat)
    (fits : pointer.toNat + amount.toNat + 7 < 2 ^ 64)
    (lower : pointer.toNat + amount.toNat ≤ next) (upper : next < pointer.toNat + amount.toNat + 8)
    (aligned : next % 8 = 0) : rounded pointer amount = BitVec.ofNat 64 next := by
  apply BitVec.eq_of_toNat_eq
  rw [rounded_nat pointer amount fits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega


end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.rounded_expected
