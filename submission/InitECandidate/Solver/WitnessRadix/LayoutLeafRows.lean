import InitECandidate.Solver.WitnessRadix.LayoutPendingRows
import InitECandidate.Solver.WitnessRadix.LayoutLeafMemory

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem leaf_primary_word {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (index ordinal : Nat) (inside : index < layout.count) :
    source.memory (cell layout .primary (8 * index)) =
      (OpenGraph.leafPost source context.dest ordinal).memory (cell layout .primary (8 * index)) := by
  have absent := data_allocation_separate layout valid allocated depth index destination .primary (Or.inl rfl)
    inside branchRoom stackRoom atLayout.incoming
  rw [← allocation_cells layout context allocated depth destination atLayout] at absent
  have away : cell layout .primary (8 * index) ≠ context.dest := by
    intro same
    rw [same] at absent
    apply absent
    simp [SplitCount.writes, SplitProgram.allocationWrites]
  change source.memory _ = StoreWord.put source.memory context.dest (WordBits.leafTag ordinal) _
  simp [StoreWord.put, away]

theorem leaf_pending_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) (ordinal : Nat)
    (tasks : List PendingStack.Task) (fits : ∀ task ∈ tasks, task.start + task.input.length ≤ layout.count)
    (rows : PendingRows source layout tasks) : PendingRows (OpenGraph.leafPost source context.dest ordinal) layout tasks := by
  intro task member
  apply BuildCopy.rows_of_agreement _ _ source.memaddrs _ _ _ _ _ (rows task member)
  intro offset bound
  have address : BuildCopy.row layout.primary (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 (0 + offset)) =
      cell layout .primary (8 * (task.start + offset)) := by
    change BuildCopy.row (base layout .primary) (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 (0 + offset)) = _
    simp only [Nat.zero_add]
    exact row_cell layout .primary task.start offset
  rw [address]
  exact leaf_primary_word source layout context allocated depth destination atLayout valid branchRoom stackRoom
    (task.start + offset) ordinal (by have := fits task member; omega)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_primary_word
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_pending_rows
