import InitECandidate.Solver.WitnessRadix.LayoutSplitMemory
import InitECandidate.Solver.WitnessRadix.LayoutDataPrefix
import InitECandidate.Solver.WitnessRadix.LayoutLeftContext
import InitECandidate.Solver.WitnessRadix.SplitRows

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem active_rows_away (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count) :
    ∀ offset < context.input.length,
      BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) ∉
        (SplitCount.writes context).map Prod.fst := by
  intro offset bound
  have indexBound : context.start + offset < layout.count := by have := atLayout.interval; omega
  have rowEq : BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
      cell layout .primary (8 * (context.start + offset)) := by
    rw [atLayout.srcEq]
    exact row_cell layout .primary context.start offset
  rw [rowEq, allocation_cells layout context allocated depth destination atLayout]
  exact data_allocation_separate layout valid allocated depth (context.start + offset) destination .primary
    (Or.inl rfl) indexBound branchRoom stackRoom atLayout.incoming

/-- After a full split, the next left task again has concrete read/write
ownership. No separate per-hash or per-store frame assumption is needed. -/
theorem left_ready {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (mapped : Mapped source layout) (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input) :
    ScatterProgram.Ready (SplitCount.post source context)
      (SplitCount.leftContext context).src (SplitCount.leftContext context).dst
      (BitVec.ofNat 64 (SplitCount.leftContext context).start) (SplitCount.leftContext context).keys
      (SplitCount.leftContext context).keyFor (SplitCount.leftContext context).input 0 (SplitCount.leftContext context).limit := by
  have allocation : context.src.toNat + 8 * context.limit < 2 ^ 64 := by
    rw [atLayout.srcEq, atLayout.limitEq]
    have bound : layout.primary.toNat + 8 * layout.capacity < 2 ^ 64 := valid.noWrap .primary
    have room := valid.room
    omega
  have fits : context.start + context.input.length ≤ context.limit := by rw [atLayout.limitEq]; exact atLayout.interval
  have children := SplitCount.child_rows source context fits allocation rows
    (active_rows_away layout context allocated depth destination atLayout valid branchRoom stackRoom)
  have immutableNext := split_immutable source layout context allocated depth destination atLayout valid branchRoom stackRoom sliceFor immutable
  have mappedNext : Mapped (SplitCount.post source context) layout := mapped
  exact context_ready (SplitCount.post source context) layout (SplitCount.leftContext context) (allocated + 1) (depth + 1)
    (leftDestination layout allocated) (left_context layout context allocated depth destination atLayout) valid mappedNext sliceFor
    immutableNext children.1

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.active_rows_away
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.left_ready
