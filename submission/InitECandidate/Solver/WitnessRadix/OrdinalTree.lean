import InitECandidate.Solver.WitnessRadix.BuildCases
import InitECandidate.Solver.WitnessRadix.PartitionRows
import InitECandidate.Solver.WitnessRadix.Graph

namespace InitECandidate.Solver.WitnessRadix.OrdinalTree

noncomputable local instance : DecidableEq ByteKeys.Key := Classical.decEq _

def entries (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (input : List (BitVec 64)) : List (ByteKeys.Key × Graph.Slice) :=
  input.map fun ordinal => (keyFor ordinal, sliceFor ordinal)

def tree (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) : Graph.Tree :=
  BuildEquations.treeAt ByteKeys.bit position (256 - position) (entries keyFor sliceFor input)

theorem filtered_entries (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) (selected : Bool) :
    (entries keyFor sliceFor input).filter (fun entry => ByteKeys.bit entry.1 position == selected) =
      entries keyFor sliceFor (input.filter fun ordinal => ByteKeys.bit (keyFor ordinal) position == selected) := by
  exact List.filter_map

theorem zero_entries (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) :
    (entries keyFor sliceFor input).filter (fun entry => !ByteKeys.bit entry.1 position) =
      entries keyFor sliceFor (input.filter fun ordinal => !ByteKeys.bit (keyFor ordinal) position) := by
  exact List.filter_map

theorem one_entries (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) :
    (entries keyFor sliceFor input).filter (fun entry => ByteKeys.bit entry.1 position) =
      entries keyFor sliceFor (input.filter fun ordinal => ByteKeys.bit (keyFor ordinal) position) := by
  exact List.filter_map

theorem terminal (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) (ordinal : BitVec 64)
    (last : input.getLast? = some ordinal) (stop : position = 256 ∨ input.length = 1) :
    tree keyFor sliceFor position input = .leaf (keyFor ordinal) (sliceFor ordinal) := by
  rcases stop with depth | single
  · subst position
    change BuildEquations.treeAt ByteKeys.bit 256 0 (entries keyFor sliceFor input) = _
    apply BuildEquations.terminal ByteKeys.bit 256 _ (keyFor ordinal, sliceFor ordinal)
    simpa only [entries, List.getLast?_map, last, Option.map_some]
  · obtain ⟨only, singleton⟩ := List.length_eq_one_iff.mp single
    subst input
    have same : only = ordinal := by simpa using last
    subst only
    exact BuildEquations.singleton _ _ _ _

theorem split (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) (inside : position < 256)
    (zeroPresent : (input.filter fun ordinal => !ByteKeys.bit (keyFor ordinal) position) ≠ [])
    (onePresent : (input.filter fun ordinal => ByteKeys.bit (keyFor ordinal) position) ≠ []) :
    tree keyFor sliceFor position input = .branch position
      (tree keyFor sliceFor (position + 1) (input.filter fun ordinal => !ByteKeys.bit (keyFor ordinal) position))
      (tree keyFor sliceFor (position + 1) (input.filter fun ordinal => ByteKeys.bit (keyFor ordinal) position)) := by
  have fuel : 256 - position = (256 - (position + 1)) + 1 := by omega
  have zeroEntries : ((entries keyFor sliceFor input).filter fun entry => !ByteKeys.bit entry.1 position) ≠ [] := by
    rw [zero_entries]
    intro empty
    exact zeroPresent (List.eq_nil_of_map_eq_nil empty)
  have oneEntries : ((entries keyFor sliceFor input).filter fun entry => ByteKeys.bit entry.1 position) ≠ [] := by
    rw [one_entries]
    intro empty
    exact onePresent (List.eq_nil_of_map_eq_nil empty)
  unfold tree
  rw [fuel, BuildEquations.split _ _ _ _ zeroEntries oneEntries, zero_entries, one_entries]

theorem unary (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (position : Nat) (input : List (BitVec 64)) (inside : position < 256)
    (uniform : ScatterProgram.zeros keyFor position input = 0 ∨
      ScatterProgram.zeros keyFor position input = input.length) :
    tree keyFor sliceFor position input = tree keyFor sliceFor (position + 1) input := by
  have fuel : 256 - position = (256 - (position + 1)) + 1 := by omega
  unfold tree
  rw [fuel]
  rcases uniform with noneZero | allZero
  · have empty : (input.filter fun ordinal => !ByteKeys.bit (keyFor ordinal) position) = [] :=
      List.length_eq_zero_iff.mp noneZero
    apply BuildEquations.unary_one
    rw [zero_entries, empty]
    rfl
  · have sum := ScatterProgram.zero_one_sum keyFor position input
    have noneOne : ScatterProgram.ones keyFor position input = 0 := by omega
    have empty : (input.filter fun ordinal => ByteKeys.bit (keyFor ordinal) position) = [] :=
      List.length_eq_zero_iff.mp noneOne
    apply BuildEquations.unary_zero
    rw [one_entries, empty]
    rfl

end InitECandidate.Solver.WitnessRadix.OrdinalTree

#print axioms InitECandidate.Solver.WitnessRadix.OrdinalTree.terminal
#print axioms InitECandidate.Solver.WitnessRadix.OrdinalTree.split

#print axioms InitECandidate.Solver.WitnessRadix.OrdinalTree.unary
