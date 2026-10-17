import InitECandidate.Solver.WitnessRadix.ConstructorData
import InitECandidate.Solver.WitnessRadix.OrdinalArray
import InitECandidate.Solver.WitnessRadix.RowsFrame

namespace InitECandidate.Solver.WitnessRadix.Constructor
open Flapjack PanSemStateFiniteExact BackingLayout

theorem prefix_le {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (left right : Nat) (within : left ≤ right)
    (prefixData : Prefix source layout keyFor right) : Prefix source layout keyFor left :=
  ⟨fun index inside => prefixData.recordWords index (by omega),
   fun index inside => prefixData.hashViews index (by omega),
   fun index inside => prefixData.ordinalWords index (by omega)⟩

theorem ordinal_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout) (keyFor : BitVec 64 → ByteKeys.Key)
    (done : Nat) (within : done ≤ layout.count) (prefixData : Prefix source layout keyFor done) :
    BuildCopy.Rows source.memory source.memaddrs layout.primary 0#64 0 (ordinals done) := by
  induction done with
  | zero => trivial
  | succ done ih =>
    have previous := ih (by omega) (prefix_le source layout keyFor done (done + 1) (by omega) prefixData)
    have ordinalAppend : ordinals (done + 1) = ordinals done ++ [BitVec.ofNat 64 done] := by
      simp [ordinals, List.range_succ, List.map_append]
    rw [ordinalAppend, BuildCopy.rows_append, ordinals_length]
    refine ⟨previous, ?_⟩
    change source.memaddrs (BuildCopy.row layout.primary 0#64 (BitVec.ofNat 64 (0 + done))) ∧ _ ∧ True
    have current : BuildCopy.row layout.primary 0#64 (BitVec.ofNat 64 (0 + done)) = cell layout .primary (8 * done) := by
      simp only [BuildCopy.row, BitVec.zero_add, Nat.zero_add, primary_cell]
    rw [current]
    refine ⟨?_, prefixData.ordinalWords done (by omega), True.intro⟩
    apply mapped .primary (8 * done) (by omega)
    change 8 * done + 8 ≤ 8 * layout.capacity
    have room := valid.room
    omega

/-- The concrete completed constructor invariant supplies all the helper's
array hypotheses, including the exact ordinal order. -/
theorem initialized_arrays {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (valid : Valid layout) (mapped : Mapped source layout)
    (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice)
    (fixedData : FixedData source layout sliceFor) (prefixData : Prefix source layout keyFor layout.count) :
    Immutable source layout keyFor sliceFor ∧
      BuildCopy.Rows source.memory source.memaddrs layout.primary 0#64 0 (ordinals layout.count) :=
  ⟨immutable_from_prefix source layout valid mapped keyFor sliceFor fixedData prefixData,
   ordinal_rows source layout valid mapped keyFor layout.count (Nat.le_refl _) prefixData⟩

end InitECandidate.Solver.WitnessRadix.Constructor

#print axioms InitECandidate.Solver.WitnessRadix.Constructor.ordinal_rows
#print axioms InitECandidate.Solver.WitnessRadix.Constructor.initialized_arrays
