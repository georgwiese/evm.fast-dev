import InitECandidate.Solver.GasBudget.MemoryExtendProgram
import InitECandidate.Solver.Arenas.Region

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

structure Geometry (base length capacity pointer scratch expand : BitVec 64) : Prop where
  capacityOrder : capacity.toNat ≤ (nextCapacity length capacity expand).toNat
  nextContains : (newLength length expand).toNat ≤ (nextCapacity length capacity expand).toNat
  nextSlack : (nextCapacity length capacity expand).toNat ≤ 2 * (newLength length expand).toNat + 1024
  nextAligned : (nextCapacity length capacity expand).toNat % 32 = 0
  deltaNat : (nextCapacity length capacity expand - capacity).toNat = (nextCapacity length capacity expand).toNat - capacity.toNat
  deltaAligned : (nextCapacity length capacity expand - capacity).toNat % 32 = 0
  extent : base.toNat + (nextCapacity length capacity expand).toNat ≤ scratch.toNat
  oldPointer : pointer = base + capacity
  newPointer : Arenas.rounded .up pointer (nextCapacity length capacity expand - capacity) = base + nextCapacity length capacity expand
  pointerAligned : pointer.toNat % 8 = 0
  clearNumber : (base + length).toNat = base.toNat + length.toNat
  clearAligned : (base + length).toNat % 8 = 0
  expandAligned : expand.toNat % 32 = 0
  clearExtent : (base + length).toNat + expand.toNat ≤ scratch.toNat

/-- Reached allocation room is supplied here by the actual allocator-normal
theorem; no expanded-buffer model is assumed. -/
theorem geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base length capacity pointer scratch expand amount : BitVec 64)
    (view : View source frame base length capacity pointer scratch) (used : Nat)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (room : Arenas.Room .up pointer scratch (nextCapacity length capacity expand - capacity)) :
    Geometry base length capacity pointer scratch expand := by
  obtain ⟨contains, forward, slack, aligned, small⟩ := capacity_bounds length capacity expand advance.natural view.depth view.slack view.capacityAligned advance.aligned advance.byteBound
  obtain ⟨delta, deltaAligned⟩ := capacity_delta length capacity expand advance.natural view.depth view.slack view.capacityAligned advance.aligned advance.byteBound
  have allocationRoom : pointer.toNat + (nextCapacity length capacity expand - capacity).toNat ≤ scratch.toNat := room
  have extent : base.toNat + (nextCapacity length capacity expand).toNat ≤ scratch.toNat := by rw [delta] at allocationRoom; have cursor := view.cursor; omega
  have capDivision := Nat.mod_add_div capacity.toNat 32
  have lenDivision := Nat.mod_add_div length.toNat 32
  have baseDivision := Nat.mod_add_div base.toNat 8
  have deltaDivision := Nat.mod_add_div (nextCapacity length capacity expand - capacity).toNat 32
  have pointerDivision := Nat.mod_add_div pointer.toNat 8
  have cursor := view.cursor
  have capAligned := view.capacityAligned
  have lengthAligned := view.lengthAligned
  have baseAligned := view.baseAligned
  have pointerAligned : pointer.toNat % 8 = 0 := by omega
  have expansionAligned : expand.toNat % 32 = 0 := by
    have nextAligned := advance.aligned
    rw [advance.natural, Nat.add_mod, lengthAligned, Nat.zero_add] at nextAligned
    simpa only [Nat.mod_mod] using nextAligned
  have oldFits : base.toNat + capacity.toNat < 2 ^ 64 := by have bound := pointer.isLt; omega
  have oldPointer : pointer = base + capacity := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_add_of_lt oldFits]
    exact cursor
  have currentExtent : base.toNat + length.toNat + expand.toNat ≤ scratch.toNat := by
    have natural := advance.natural
    change (newLength length expand).toNat = length.toNat + expand.toNat at natural
    omega
  have baseLengthFits : base.toNat + length.toNat < 2 ^ 64 := by have bound := scratch.isLt; omega
  have clearNumber := BitVec.toNat_add_of_lt baseLengthFits
  have clearAligned : (base + length).toNat % 8 = 0 := by rw [clearNumber]; omega
  obtain ⟨_, _, roundedLow, roundedHigh, roundedNear, roundedAligned⟩ :=
    Arenas.upward_guards pointer scratch (nextCapacity length capacity expand - capacity) view.scratchAligned room
  have sumAligned : (pointer.toNat + (nextCapacity length capacity expand - capacity).toNat) % 8 = 0 := by
    have sumDivision := Nat.mod_add_div (pointer.toNat + (nextCapacity length capacity expand - capacity).toNat) 8
    omega
  have roundedNumber : (Arenas.rounded .up pointer (nextCapacity length capacity expand - capacity)).toNat =
      pointer.toNat + (nextCapacity length capacity expand - capacity).toNat := by
    have roundedDivision := Nat.mod_add_div (Arenas.rounded .up pointer (nextCapacity length capacity expand - capacity)).toNat 8
    have sumDivision := Nat.mod_add_div (pointer.toNat + (nextCapacity length capacity expand - capacity).toNat) 8
    omega
  have nextFits : base.toNat + (nextCapacity length capacity expand).toNat < 2 ^ 64 := by have bound := scratch.isLt; omega
  have newPointer : Arenas.rounded .up pointer (nextCapacity length capacity expand - capacity) = base + nextCapacity length capacity expand := by
    apply BitVec.eq_of_toNat_eq
    rw [roundedNumber, BitVec.toNat_add_of_lt nextFits, delta, cursor]
    omega
  exact ⟨forward, contains, slack, aligned, delta, deltaAligned, extent, oldPointer, newPointer, pointerAligned,
    clearNumber, clearAligned, expansionAligned, by rw [clearNumber]; exact currentExtent⟩

theorem View.header_outside {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frame base length capacity pointer scratch : BitVec 64}
    (view : View source frame base length capacity pointer scratch) (offset : Nat) (inside : offset ≤ 272) :
    Arenas.Outside base scratch (frame + BitVec.ofNat 64 offset) := by
  apply Or.inr
  have fits : frame.toNat + (BitVec.ofNat 64 offset).toNat < 2 ^ 64 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have bound := view.frameFits; omega)]
    have bound := view.frameFits
    omega
  rw [BitVec.toNat_add_of_lt fits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have bound := view.frameFits; omega)]
  have high := view.frameAbove
  omega

theorem zero_away (memory : WordWrites.Memory) (base scratch destination query : BitVec 64) (count : Nat)
    (lower : base.toNat ≤ destination.toNat) (upper : destination.toNat + count ≤ scratch.toNat)
    (outside : Arenas.Outside base scratch query) :
    Zero.finalMemory memory destination count query = memory query := by
  apply Zero.final_memory_away
  intro offset inside equal
  have number := byteAddress_toNat destination offset (by have bound := scratch.isLt; omega)
  have same := congrArg BitVec.toNat equal
  rw [number] at same
  rcases outside with before | after <;> omega

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.geometry
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.View.header_outside
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.zero_away
