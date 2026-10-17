import InitECandidate.Solver.WitnessRadix.LayoutFrontierSlots
import InitECandidate.Solver.WitnessRadix.LayoutGraphFrame

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem new_branch_safe {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (zero one : Graph.Tree) :
    OpenGraph.SafeFrontier source layout.table layout.keys layout.vals (SplitCount.branchReplacement context zero one) := by
  have incoming : Incoming layout allocated context.dest :=
    ⟨destination.1, destination.2, atLayout.incoming, atLayout.destEq⟩
  have nodeEq : context.node = cell layout .keys (32 * layout.count + 24 * allocated + 8 * 0) := by
    simpa using context_node_cell layout context allocated depth destination atLayout 0
  have fieldSafe (field : Nat) (selected : field = 1 ∨ field = 2) :
      ¬ OpenGraph.reads source layout.table layout.keys layout.vals (SplitCount.branchReplacement context zero one)
        (context.node + BitVec.ofNat 64 (8 * field)) := by
    have fieldBound : field < 3 := by rcases selected with rfl | rfl <;> decide
    have fieldNonzero : field ≠ 0 := by rcases selected with rfl | rfl <;> decide
    have childEq := context_node_cell layout context allocated depth destination atLayout field
    intro read
    have either : context.node + BitVec.ofNat 64 (8 * field) = context.dest ∨
        context.node + BitVec.ofNat 64 (8 * field) = context.node := by
      simpa only [SplitCount.branchReplacement, OpenGraph.reads, or_false] using read
    rcases either with destRead | nodeRead
    · exact protected_fresh layout valid allocated branchRoom context.dest
        (incoming_protected layout allocated context.dest incoming) field fieldBound (destRead.symm.trans childEq)
    · exact branch_fields_ne layout valid allocated branchRoom field 0 fieldBound (by decide) fieldNonzero
        (childEq.symm.trans (nodeRead.trans nodeEq))
  intro entry member read
  simp only [SplitCount.branchReplacement, OpenGraph.frontier, List.singleton_append, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact fieldSafe 1 (Or.inl rfl) read
  · exact fieldSafe 2 (Or.inr rfl) read

/-- A real split preserves safety of every remaining frontier store using
fresh branch slots and the old located/distinct frontier invariant. -/
theorem split_frontier_safe {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (zero one : Graph.Tree) (before after : OpenGraph.Tree)
    (step : OpenGraph.FillFirst context.dest (.branch context.position zero one)
      (SplitCount.branchReplacement context zero one) before after)
    (located : Located layout allocated before)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals before)
    (distinct : ((OpenGraph.frontier before).map Prod.fst).Nodup) :
    OpenGraph.SafeFrontier (SplitCount.post source context) layout.table layout.keys layout.vals after := by
  have active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier before := by
    obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
    exact ⟨.branch context.position zero one, by rw [oldFrontier]; exact List.mem_cons_self⟩
  have agreement := split_graph_agreement source layout context allocated depth destination atLayout valid branchRoom stackRoom
    sliceFor immutable before located safe active
  apply OpenGraph.fill_safe source (SplitCount.post source context) layout.table layout.keys layout.vals step distinct safe agreement
    (new_branch_safe (SplitCount.post source context) layout context allocated depth destination atLayout valid branchRoom zero one)
  · have freshField (field : Nat) (fieldBound : field < 3) :
        ¬ OpenGraph.reads source layout.table layout.keys layout.vals before (context.node + BitVec.ofNat 64 (8 * field)) := by
      intro read
      have protectedRead := located_reads source layout allocated valid context.keyFor sliceFor immutable before located _ read
      exact protected_fresh layout valid allocated branchRoom _ protectedRead field fieldBound
        (context_node_cell layout context allocated depth destination atLayout field)
    intro entry member
    simp only [SplitCount.branchReplacement, OpenGraph.frontier, List.singleton_append, List.mem_cons,
      List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact freshField 1 (by decide)
    · exact freshField 2 (by decide)
  · intro entry member different read
    have either : entry.1 = context.dest ∨ entry.1 = context.node := by
      simpa only [SplitCount.branchReplacement, OpenGraph.reads, or_false] using read
    rcases either with destRead | nodeRead
    · exact different destRead
    · have nodeEq : context.node = cell layout .keys (32 * layout.count + 24 * allocated + 8 * 0) := by
        simpa using context_node_cell layout context allocated depth destination atLayout 0
      exact fresh_frontier_slot layout valid allocated branchRoom before located entry member 0 (by decide) (nodeRead.trans nodeEq)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.new_branch_safe
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_frontier_safe
