import InitECandidate.Solver.MutableTable.InsertLookup

namespace InitECandidate.Solver.MutableTable.Insert
open Flapjack PanSemStateFiniteExact

/-- A real present lookup result has an actual used byte1 and belongs to the
occupied covering list. This follows from the physical binary representation. -/
theorem GeneralData.selected_slot (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count : BitVec 64) (bits : Nat) (items : List Nat)
    (data : GeneralData source table p kind vals order position count bits items) (index : BitVec 64)
    (selected : Find.Selection source p index) (present : index ≠ p.capacity) :
    Find.usedByte source p index = some 1 ∧ index.toNat ∈ items := by
  rcases selected with absent | ⟨inside, byte, nonzero, loaded⟩
  · exact False.elim (present absent)
  · have capNumber : p.capacity.toNat = 2 ^ bits := by
      rw [data.capacity, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by decide) data.small)]
    have bounded : index.toNat < 2 ^ bits := by rwa [← capNumber]
    have binary : Find.usedByte source p index = some 0 ∨ Find.usedByte source p index = some 1 := by
      simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using data.binary index.toNat bounded
    have one : Find.usedByte source p index = some 1 := by
      rcases binary with zero | one
      · exact False.elim (nonzero (Option.some.inj (loaded.symm.trans zero)))
      · exact one
    refine ⟨one, data.covered index.toNat bounded ?_⟩
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using one

/-- Physical empty occupancy forces the real lookup result to be absent. -/
theorem GeneralData.empty_selection (source : PanSemStateFiniteExact 64 Guest.HostMemory) (table : BitVec 64) (p : Find.Parameters)
    (kind : KeyHash.Kind) (vals order position count : BitVec 64) (bits : Nat)
    (data : GeneralData source table p kind vals order position count bits []) (index : BitVec 64)
    (selected : Find.Selection source p index) : index = p.capacity := by
  by_contra present
  have member := (GeneralData.selected_slot source table p kind vals order position count bits [] data index selected present).2
  cases member

end InitECandidate.Solver.MutableTable.Insert

#print axioms InitECandidate.Solver.MutableTable.Insert.GeneralData.selected_slot
#print axioms InitECandidate.Solver.MutableTable.Insert.GeneralData.empty_selection
