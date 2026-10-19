import InitECandidate.Solver.GasBudget.StackPushGrowthCall
import InitECandidate.Solver.Arenas.Region

namespace InitECandidate.Solver.GasBudget.StackPush
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

theorem GrowthView.destination_bounds {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base scratch memory capacity : BitVec 64} (view : GrowthView source frame base scratch memory capacity) :
    memory.toNat ≤ (growDestination scratch capacity).toNat ∧
      (growDestination scratch capacity).toNat + 64 * capacity.toNat ≤ scratch.toNat ∧
      (growDestination scratch capacity).toNat % 8 = 0 := by
  obtain ⟨_, _, low, high, _, aligned⟩ := Arenas.downward_guards scratch memory ((capacity * 2#64) * 32#64) view.arenaAligned view.room
  obtain ⟨_, _, _, allocation, _⟩ := grow_numbers capacity view.positive view.bounded
  rw [allocation] at high
  exact ⟨low, high, aligned⟩

/-- Every copy destination, including byte-aligned backing words, lies
inside the actual fresh scratch allocation. Older owned words are protected. -/
theorem GrowthView.copy_away {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base scratch memory capacity : BitVec 64} (view : GrowthView source frame base scratch memory capacity)
    (query : BitVec 64) (outside : Arenas.Outside memory scratch query) :
    CopyGeneral.Away (growDestination scratch capacity) query (32 * capacity.toNat) := by
  obtain ⟨low, high, aligned⟩ := view.destination_bounds
  have scratchBound := scratch.isLt
  intro offset inside
  have offsetBound : offset < 2 ^ 64 := by omega
  have number : (byteAddress (growDestination scratch capacity) offset).toNat = (growDestination scratch capacity).toNat + offset := by
    unfold byteAddress
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt offsetBound, Nat.mod_eq_of_lt (by omega)]
  have backing : (panByteAlignHOL (width := 64) (byteAddress (growDestination scratch capacity) offset)).toNat =
      ((growDestination scratch capacity).toNat + offset) / 8 * 8 := by
    change (BitVec.ofNat 64 ((byteAddress (growDestination scratch capacity) offset).toNat / 8 * 8)).toNat = _
    rw [BitVec.toNat_ofNat, number, Nat.mod_eq_of_lt (by omega)]
  have whole := Nat.mod_add_div ((growDestination scratch capacity).toNat + offset) 8
  have start := Nat.mod_add_div (growDestination scratch capacity).toNat 8
  have remainder := Nat.mod_lt ((growDestination scratch capacity).toNat + offset) (by decide : 0 < 8)
  constructor
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [number] at same
    rcases outside with before | after <;> omega
  · intro equal
    have same := congrArg BitVec.toNat equal
    rw [backing] at same
    rcases outside with before | after <;> omega

theorem GrowthView.slot_away {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {frame base scratch memory capacity : BitVec 64} (view : GrowthView source frame base scratch memory capacity)
    (query : BitVec 64) (outside : Arenas.Outside memory scratch query) (index : Nat) (inside : index < 4) :
    query ≠ (growDestination scratch capacity + capacity * 32#64) + BitVec.ofNat 64 (8 * index) := by
  obtain ⟨low, high, aligned⟩ := view.destination_bounds
  obtain ⟨_, _, _, _, copied⟩ := grow_numbers capacity view.positive view.bounded
  have positive := view.positive
  have scratchBound := scratch.isLt
  have firstFits : (growDestination scratch capacity).toNat + (capacity * 32#64).toNat < 2 ^ 64 := by rw [copied]; omega
  have first := BitVec.toNat_add_of_lt firstFits
  have indexFits : 8 * index < 2 ^ 64 := by omega
  have secondFits : (growDestination scratch capacity + capacity * 32#64).toNat + (BitVec.ofNat 64 (8 * index)).toNat < 2 ^ 64 := by
    rw [first, copied, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexFits]
    omega
  intro equal
  have same := congrArg BitVec.toNat equal
  rw [BitVec.toNat_add_of_lt secondFits, first, copied, BitVec.toNat_ofNat, Nat.mod_eq_of_lt indexFits] at same
  rcases outside with before | after <;> omega

end InitECandidate.Solver.GasBudget.StackPush

#print axioms InitECandidate.Solver.GasBudget.StackPush.GrowthView.destination_bounds
#print axioms InitECandidate.Solver.GasBudget.StackPush.GrowthView.copy_away
#print axioms InitECandidate.Solver.GasBudget.StackPush.GrowthView.slot_away
