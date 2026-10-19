import InitECandidate.Solver.GasBudget.MemoryExpansionCostAffordable

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack

def newLength (length expand : BitVec 64) : BitVec 64 := length + expand
def chosenCapacity (length capacity expand : BitVec 64) : BitVec 64 :=
  if capacity * 2#64 < newLength length expand then newLength length expand + 1024#64 else capacity * 2#64
def nextCapacity (length capacity expand : BitVec 64) : BitVec 64 :=
  if capacity < newLength length expand then chosenCapacity length capacity expand else capacity

/-- Exact arithmetic of the original doubling/fallback capacity branch.
The current slack invariant and affordable next-length ceiling prevent every
unsigned wrap before an actual allocator is reached. -/
theorem capacity_nat (length capacity expand : BitVec 64)
    (natural : (newLength length expand).toNat = length.toNat + expand.toNat)
    (slack : capacity.toNat ≤ 2 * length.toNat + 1024)
    (bounded : (newLength length expand).toNat ≤ 178956960) :
    (nextCapacity length capacity expand).toNat =
      if capacity.toNat < (newLength length expand).toNat then
        if 2 * capacity.toNat < (newLength length expand).toNat then (newLength length expand).toNat + 1024 else 2 * capacity.toNat
      else capacity.toNat := by
  have capBound : capacity.toNat ≤ 357914944 := by omega
  have doubled : (capacity * 2#64).toNat = 2 * capacity.toNat := by
    rw [BitVec.toNat_mul]
    change (capacity.toNat * 2) % (2 ^ 64) = _
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have appendFits : (newLength length expand).toNat + (1024#64 : BitVec 64).toNat < 2 ^ 64 := by change (newLength length expand).toNat + 1024 < 2 ^ 64; omega
  unfold nextCapacity chosenCapacity
  by_cases grow : capacity < newLength length expand
  · have growNat : capacity.toNat < (newLength length expand).toNat := grow
    rw [if_pos grow, if_pos growNat]
    by_cases fallback : capacity * 2#64 < newLength length expand
    · have fallbackNat : 2 * capacity.toNat < (newLength length expand).toNat := by change (capacity * 2#64).toNat < _ at fallback; rw [doubled] at fallback; exact fallback
      rw [if_pos fallback, if_pos fallbackNat, BitVec.toNat_add_of_lt appendFits]
      rfl
    · have noFallback : ¬2 * capacity.toNat < (newLength length expand).toNat := by change ¬(capacity * 2#64).toNat < _ at fallback; rw [doubled] at fallback; exact fallback
      rw [if_neg fallback, if_neg noFallback, doubled]
  · have noGrowth : ¬capacity.toNat < (newLength length expand).toNat := grow
    rw [if_neg grow, if_neg noGrowth]

theorem capacity_bounds (length capacity expand : BitVec 64)
    (natural : (newLength length expand).toNat = length.toNat + expand.toNat)
    (depth : length.toNat ≤ capacity.toNat) (slack : capacity.toNat ≤ 2 * length.toNat + 1024)
    (aligned : capacity.toNat % 32 = 0) (nextAligned : (newLength length expand).toNat % 32 = 0)
    (bounded : (newLength length expand).toNat ≤ 178956960) :
    (newLength length expand).toNat ≤ (nextCapacity length capacity expand).toNat ∧
      capacity.toNat ≤ (nextCapacity length capacity expand).toNat ∧
      (nextCapacity length capacity expand).toNat ≤ 2 * (newLength length expand).toNat + 1024 ∧
      (nextCapacity length capacity expand).toNat % 32 = 0 ∧
      (nextCapacity length capacity expand).toNat ≤ 357914944 := by
  rw [capacity_nat length capacity expand natural slack bounded]
  split_ifs with grow fallback
  all_goals refine ⟨by omega, by omega, by omega, ?_, by omega⟩
  · simp [Nat.add_mod, nextAligned]
  · simp [Nat.mul_mod, aligned]
  · exact aligned

theorem capacity_delta (length capacity expand : BitVec 64)
    (natural : (newLength length expand).toNat = length.toNat + expand.toNat)
    (depth : length.toNat ≤ capacity.toNat) (slack : capacity.toNat ≤ 2 * length.toNat + 1024)
    (aligned : capacity.toNat % 32 = 0) (nextAligned : (newLength length expand).toNat % 32 = 0)
    (bounded : (newLength length expand).toNat ≤ 178956960) :
    (nextCapacity length capacity expand - capacity).toNat = (nextCapacity length capacity expand).toNat - capacity.toNat ∧
      (nextCapacity length capacity expand - capacity).toNat % 32 = 0 := by
  obtain ⟨contains, forward, boundedNext, alignedNext, small⟩ := capacity_bounds length capacity expand natural depth slack aligned nextAligned bounded
  have order : capacity ≤ nextCapacity length capacity expand := forward
  have delta := BitVec.toNat_sub_of_le order
  refine ⟨delta, ?_⟩
  rw [delta]
  have beforeDivision := Nat.mod_add_div capacity.toNat 32
  have afterDivision := Nat.mod_add_div (nextCapacity length capacity expand).toNat 32
  omega

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.capacity_nat
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.capacity_bounds
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.capacity_delta
