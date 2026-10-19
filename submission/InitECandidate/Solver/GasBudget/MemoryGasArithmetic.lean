import InitECandidate.Solver.GasBudget.MemoryGasCostValue

namespace InitECandidate.Solver.GasBudget.MemoryGasCost
open Flapjack

/-- A small old cost plus a small observed unsigned delta cannot hide a
wrap. This does not assume monotonicity of an unproved mathematical cost. -/
theorem delta_exact (old fresh : BitVec 64) (limit : Nat) (small : 2 * limit < 2 ^ 64)
    (oldBound : old.toNat ≤ limit) (deltaBound : (fresh - old).toNat ≤ limit) :
    fresh.toNat = old.toNat + (fresh - old).toNat := by
  have fits : old.toNat + (fresh - old).toNat < 2 ^ 64 := by omega
  have wordEq : old + (fresh - old) = fresh := by rw [BitVec.add_comm]; exact BitVec.sub_add_cancel _ _
  have number := congrArg BitVec.toNat wordEq
  rw [BitVec.toNat_add_of_lt fits] at number
  exact number.symm

theorem charge_covers (old fresh amount : BitVec 64) (used gas : Nat)
    (covered : old.toNat ≤ used) (pool : used + gas ≤ 16777216) (affordable : amount.toNat ≤ gas)
    (delta : (fresh - old).toNat ≤ amount.toNat) :
    fresh.toNat ≤ used + amount.toNat ∧ old.toNat ≤ fresh.toNat ∧ (fresh - old).toNat = fresh.toNat - old.toNat := by
  have exactDelta := delta_exact old fresh 16777216 (by decide) (by omega) (by omega)
  omega

/-- Conditional aggregate expansion-size accounting. Actual live/retired
frame sizes and their cost budget must still be supplied by reachability. -/
theorem aligned_sum (sizes : List (BitVec 64))
    (aligned : ∀ size ∈ sizes, size.toNat % 32 = 0) :
    3 * (sizes.map BitVec.toNat).sum ≤ 32 * (sizes.map (fun size => (resultWord size).toNat)).sum := by
  induction sizes with
  | nil => simp
  | cons head rest ih =>
    have lowerHead := lower head
    have headAligned := aligned head (by simp)
    have headDivision := Nat.mod_add_div head.toNat 32
    have tail := ih (by intro size member; exact aligned size (List.mem_cons_of_mem _ member))
    change 3 * (head.toNat + (rest.map BitVec.toNat).sum) ≤
      32 * ((resultWord head).toNat + (rest.map (fun size => (resultWord size).toNat)).sum)
    omega

theorem aligned_sum_mod (sizes : List (BitVec 64))
    (aligned : ∀ size ∈ sizes, size.toNat % 32 = 0) : (sizes.map BitVec.toNat).sum % 32 = 0 := by
  induction sizes with
  | nil => simp
  | cons head rest ih =>
    have tail := ih (by intro size member; exact aligned size (List.mem_cons_of_mem _ member))
    simp only [List.map_cons, List.sum_cons, Nat.add_mod, aligned head (by simp), tail, Nat.zero_add, Nat.zero_mod]

theorem aligned_byte_sum_bound (sizes : List (BitVec 64))
    (aligned : ∀ size ∈ sizes, size.toNat % 32 = 0)
    (cap : (sizes.map (fun size => (resultWord size).toNat)).sum ≤ 16777216) :
    (sizes.map BitVec.toNat).sum ≤ 178956960 := by
  have covered := aligned_sum sizes aligned
  have multiple := aligned_sum_mod sizes aligned
  omega

end InitECandidate.Solver.GasBudget.MemoryGasCost

#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.delta_exact
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.charge_covers
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.aligned_sum
#print axioms InitECandidate.Solver.GasBudget.MemoryGasCost.aligned_byte_sum_bound
