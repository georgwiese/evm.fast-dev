import InitECandidate.Solver.WitnessRadix.LayoutDataPrefix
import InitECandidate.Solver.WitnessRadix.RowsFrame

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem inactive_primary_word {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (index : Nat) (indexBound : index < layout.count)
    (inactive : ∀ offset < context.input.length, index ≠ context.start + offset) :
    source.memory (cell layout .primary (8 * index)) = (SplitCount.post source context).memory (cell layout .primary (8 * index)) := by
  have room := valid.room
  apply Eq.symm
  apply SplitCount.post_away source context (cell layout .primary (8 * index))
  · intro offset bound
    have rowEq : BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .primary (8 * (context.start + offset)) := by
      rw [atLayout.srcEq]
      exact row_cell layout .primary context.start offset
    rw [rowEq]
    exact cell_injective layout valid .primary _ _ (by change _ < 8 * layout.capacity; omega)
      (by change _ < 8 * layout.capacity; have := atLayout.interval; omega) (by have := inactive offset bound; omega)
  · intro offset bound
    have rowEq : BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .backup (8 * (context.start + offset)) := by
      rw [atLayout.dstEq]
      exact row_cell layout .backup context.start offset
    rw [rowEq]
    exact valid.separate .primary .backup (by decide) _ (by change _ < 8 * layout.capacity; omega)
      _ (by change _ < 8 * layout.capacity; have := atLayout.interval; omega)
  · rw [allocation_cells layout context allocated depth destination atLayout]
    exact data_allocation_separate layout valid allocated depth index destination .primary (Or.inl rfl)
      indexBound branchRoom stackRoom atLayout.incoming

/-- A split preserves the exact readable primary interval owned by any
pending sibling whose record interval is disjoint from the active task. -/
theorem other_interval_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (start : Nat) (input : List (BitVec 64)) (fits : start + input.length ≤ layout.count)
    (disjoint : start + input.length ≤ context.start ∨ context.start + context.input.length ≤ start)
    (rows : BuildCopy.Rows source.memory source.memaddrs layout.primary (BitVec.ofNat 64 start) 0 input) :
    BuildCopy.Rows (SplitCount.post source context).memory (SplitCount.post source context).memaddrs
      layout.primary (BitVec.ofNat 64 start) 0 input := by
  apply BuildCopy.rows_of_agreement _ _ source.memaddrs _ _ _ _ _ rows
  intro offset bound
  have address : BuildCopy.row layout.primary (BitVec.ofNat 64 start) (BitVec.ofNat 64 (0 + offset)) =
      cell layout .primary (8 * (start + offset)) := by
    change BuildCopy.row (base layout .primary) (BitVec.ofNat 64 start) (BitVec.ofNat 64 (0 + offset)) = _
    simp only [Nat.zero_add]
    exact row_cell layout .primary start offset
  rw [address]
  apply inactive_primary_word source layout context allocated depth destination atLayout valid branchRoom stackRoom
    (start + offset) (by omega)
  intro activeOffset activeBound
  rcases disjoint with before | after <;> omega

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.inactive_primary_word
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.other_interval_rows
