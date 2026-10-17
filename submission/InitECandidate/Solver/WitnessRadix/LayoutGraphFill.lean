import InitECandidate.Solver.WitnessRadix.LayoutGraphFrame
import InitECandidate.Solver.WitnessRadix.LayoutSplitInputs
import InitECandidate.Solver.WitnessRadix.SplitGraphFill
import InitECandidate.Solver.WitnessRadix.SplitLoop

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- One complete actual split body installs its branch in the represented
partial graph. All per-read and per-store obligations follow from the shared
layout, immutable records, task ownership and safe located frontier. -/
theorem execute_split_graph {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (mapped : Mapped source layout) (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (locals : SplitCount.TaskLocals source context)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (inside : context.position < 256) (splitZero : 0 < zeroCount context)
    (splitOne : zeroCount context < context.input.length) (enough : 3 * context.input.length ≤ source.clock)
    (zero one : Graph.Tree) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest (.branch context.position zero one)
      (SplitCount.branchReplacement context zero one) before after)
    (rep : OpenGraph.Represents source layout.table layout.keys layout.vals before)
    (located : Located layout allocated before)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals before) :
    evaluateHOLFiniteState source BuildEntry.mainBody = (none, SplitCount.post source context) ∧
      OpenGraph.Represents (SplitCount.post source context) layout.table layout.keys layout.vals after ∧
      OpenGraph.expected after = OpenGraph.expected before := by
  have premises := split_inputs source layout context allocated depth destination atLayout valid mapped branchRoom stackRoom
    sliceFor immutable locals rows inside splitZero splitOne enough
  have active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier before := by
    obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
    exact ⟨.branch context.position zero one, by rw [oldFrontier]; exact List.mem_cons_self⟩
  have agreement := split_graph_agreement source layout context allocated depth destination atLayout valid branchRoom stackRoom
    sliceFor immutable before located safe active
  have nonzero : context.node ≠ 0#64 := by rw [atLayout.nodeEq]; exact branch_nonzero layout valid allocated branchRoom
  have even : context.node &&& 1#64 = 0#64 := by rw [atLayout.nodeEq]; exact branch_even layout valid allocated branchRoom
  refine ⟨SplitCount.main_body_split source context premises (by omega), ?_,
    OpenGraph.replacement_expected (OpenGraph.fill_replaces step) rfl⟩
  exact OpenGraph.replacement_represents source (SplitCount.post source context) rfl rfl layout.table layout.keys layout.vals
    (OpenGraph.fill_replaces step) rfl
    (SplitCount.new_branch source context layout.table layout.keys layout.vals zero one
      (allocation_distinct layout context allocated depth destination atLayout valid branchRoom stackRoom)
      premises.mapped nonzero even inside) agreement rep

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.execute_split_graph
