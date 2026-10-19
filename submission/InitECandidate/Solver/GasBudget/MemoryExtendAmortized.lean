import InitECandidate.Solver.GasBudget.MemoryExtendCall

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

def potential (length capacity : BitVec 64) : Nat := capacity.toNat / 32 + length.toNat / 32

/-- The two actual clear loops telescope against allocated capacity and
logical length. The constant covers allocation and both helper call sites. -/
theorem price_potential (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used) :
    price length capacity expand + potential length capacity ≤
      potential (newLength length expand) (nextCapacity length capacity expand) + 3 := by
  obtain ⟨contains, forward, slack, aligned, small⟩ := capacity_bounds length capacity expand advance.natural view.depth view.slack view.capacityAligned advance.aligned advance.byteBound
  obtain ⟨delta, deltaAligned⟩ := capacity_delta length capacity expand advance.natural view.depth view.slack view.capacityAligned advance.aligned advance.byteBound
  have natural := advance.natural
  change (newLength length expand).toNat = length.toNat + expand.toNat at natural
  have oldAligned := view.capacityAligned
  have oldLengthAligned := view.lengthAligned
  have nextLengthAligned := advance.aligned
  change (newLength length expand).toNat % 32 = 0 at nextLengthAligned
  have capDivision := Nat.mod_add_div capacity.toNat 32
  have lengthDivision := Nat.mod_add_div length.toNat 32
  have nextCapDivision := Nat.mod_add_div (nextCapacity length capacity expand).toNat 32
  have nextLengthDivision := Nat.mod_add_div (newLength length expand).toNat 32
  have deltaDivision := Nat.mod_add_div (nextCapacity length capacity expand - capacity).toNat 32
  by_cases zero : expand = 0#64
  · rw [price, if_pos zero]
    unfold potential
    omega
  · rw [price, if_neg zero]
    unfold bodyPrice growthPrice potential
    split <;> omega

theorem potential_length (length capacity : BitVec 64)
    (aligned : length.toNat % 32 = 0) (slack : capacity.toNat ≤ 2 * length.toNat + 1024) :
    potential length capacity ≤ 3 * (length.toNat / 32) + 32 := by
  have division := Nat.mod_add_div length.toNat 32
  unfold potential
  omega

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.price_potential
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.potential_length
