import InitECandidate.Solver.WitnessRadix.InvariantClock
import InitECandidate.Solver.WitnessRadix.AgendaBudget
import InitECandidate.Solver.WitnessRadix.OpenGraphSelect
import InitECandidate.Solver.WitnessRadix.LayoutGraphFill
import InitECandidate.Solver.WitnessRadix.LayoutBranchSafety
import InitECandidate.Solver.WitnessRadix.LayoutBranchFrontier
import InitECandidate.Solver.WitnessRadix.LayoutStackPush

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- The complete actual split body preserves the full construction invariant,
including its physical pending stack, readable intervals and expected graph. -/
theorem invariant_split {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (tasks : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination tasks graph)
    (inside : context.position < 256) (splitZero : 0 < zeroCount context) (splitOne : zeroCount context < context.input.length)
    (enough : 3 * context.input.length ≤ source.clock) :
    ∃ nextGraph,
      evaluateHOLFiniteState source BuildEntry.mainBody = (none, SplitCount.post source context) ∧
      Invariant (SplitCount.post source context) layout sliceFor expectedTree (allocated + 1) completed (depth + 1)
        (SplitCount.leftContext context) (leftDestination layout allocated) (PendingStack.rightTask context :: tasks) nextGraph := by
  have branchRoom := invariant_branch_room source layout sliceFor expectedTree allocated completed depth context destination tasks graph inv
  have stackRoom := invariant_stack_room source layout sliceFor expectedTree allocated completed depth context destination tasks graph inv
  have zeroPresent : (context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal) ≠ [] :=
    List.length_pos_iff.mp splitZero
  have sum := ScatterProgram.zero_one_sum context.keyFor context.position context.input
  have onePositive : 0 < ScatterProgram.ones context.keyFor context.position context.input := by
    change zeroCount context + ScatterProgram.ones context.keyFor context.position context.input = context.input.length at sum
    omega
  have onePresent : (context.input.filter (ScatterProgram.keep context.keyFor context.position)) ≠ [] :=
    List.length_pos_iff.mp onePositive
  let zeroTree := OrdinalTree.tree context.keyFor sliceFor (context.position + 1)
    (context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal)
  let oneTree := OrdinalTree.tree context.keyFor sliceFor (context.position + 1)
    (context.input.filter (ScatterProgram.keep context.keyFor context.position))
  have treeEq : currentTree context sliceFor = .branch context.position zeroTree oneTree :=
    OrdinalTree.split context.keyFor sliceFor context.position context.input inside zeroPresent onePresent
  obtain ⟨nextGraph, step⟩ := OpenGraph.fill_first_exists graph context.dest (currentTree context sliceFor)
    (splitReplacement context sliceFor) (tasks.map (savedHole context.keyFor sliceFor)) inv.aligned
  have branchStep : OpenGraph.FillFirst context.dest (.branch context.position zeroTree oneTree)
      (SplitCount.branchReplacement context zeroTree oneTree) graph nextGraph := by
    rw [← treeEq]
    exact step
  have execution := execute_split_graph source layout context allocated depth destination inv.atLayout valid inv.mapped branchRoom stackRoom
    sliceFor inv.immutable inv.locals inv.rows inside splitZero splitOne enough zeroTree oneTree graph nextGraph branchStep
    inv.represented inv.located inv.safe
  have nextExpected := OpenGraph.replacement_expected (OpenGraph.fill_replaces step) treeEq.symm
  have allocation : context.src.toNat + 8 * context.limit < 2 ^ 64 := by
    rw [inv.atLayout.srcEq, inv.atLayout.limitEq]
    have bound : layout.primary.toNat + 8 * layout.capacity < 2 ^ 64 := valid.noWrap .primary
    have room := valid.room
    omega
  have fits : context.start + context.input.length ≤ context.limit := by rw [inv.atLayout.limitEq]; exact inv.atLayout.interval
  have children := SplitCount.child_rows source context fits allocation inv.rows
    (active_rows_away layout context allocated depth destination inv.atLayout valid branchRoom stackRoom)
  refine ⟨nextGraph, execution.1, ?_⟩
  refine ⟨inv.mapped,
    split_immutable source layout context allocated depth destination inv.atLayout valid branchRoom stackRoom sliceFor inv.immutable,
    left_context layout context allocated depth destination inv.atLayout,
    SplitCount.post_locals source context inv.locals, children.1, zeroPresent, (by change context.position + 1 ≤ 256; omega),
    (by simp only [List.length_cons, inv.length]),
    valid_pending_push layout context allocated depth destination inv.atLayout inside splitOne tasks inv.pendingValid,
    pushed_parents layout context allocated depth destination inv.atLayout tasks inv.parents,
    split_stack_represents source layout context allocated depth destination inv.atLayout valid inv.mapped branchRoom stackRoom tasks inv.length inv.parents inv.stack,
    split_pending_rows source layout context allocated depth destination inv.atLayout valid branchRoom stackRoom inv.rows tasks
      (fun task member => (inv.pendingValid task member).interval) inv.ordered inv.pendingRows,
    ?_, execution.2.1,
    split_located layout context allocated depth destination inv.atLayout zeroTree oneTree graph nextGraph branchStep inv.located,
    split_frontier_safe source layout context allocated depth destination inv.atLayout valid branchRoom stackRoom sliceFor inv.immutable
      zeroTree oneTree graph nextGraph branchStep inv.located inv.safe inv.distinct,
    split_frontier_distinct layout context allocated depth destination inv.atLayout valid branchRoom zeroTree oneTree graph nextGraph branchStep inv.located inv.distinct,
    split_aligned context sliceFor tasks graph nextGraph inv.aligned step,
    nextExpected.trans inv.expected,
    (OpenGraph.replacement_slot (OpenGraph.fill_replaces step) rfl).trans inv.root, split_agenda_budget layout context tasks completed allocated inv.budget splitZero splitOne⟩
  exact PendingStack.ordered_push context tasks inv.ordered

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_split
