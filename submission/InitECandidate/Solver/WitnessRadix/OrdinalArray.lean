import InitECandidate.Solver.WitnessRadix.HelperBuilt

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

def ordinals (count : Nat) : List (BitVec 64) := (List.range count).map (BitVec.ofNat 64)

theorem ordinals_length (count : Nat) : (ordinals count).length = count := by simp [ordinals]

theorem ordinal_inside (count : Nat) (small : count < 2 ^ 64) (ordinal : BitVec 64) (member : ordinal ∈ ordinals count) :
    ordinal.toNat < count := by
  obtain ⟨index, indexMember, rfl⟩ := List.mem_map.mp member
  have inside : index < count := List.mem_range.mp indexMember
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans inside small)]
  exact inside

theorem ordinal_entries (count : Nat) (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) :
    OrdinalTree.entries keyFor sliceFor (ordinals count) =
      (List.range count).map (fun index => (keyFor (BitVec.ofNat 64 index), sliceFor (BitVec.ofNat 64 index))) := by
  simp [OrdinalTree.entries, ordinals, List.map_map]

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.ordinal_inside
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.ordinal_entries
