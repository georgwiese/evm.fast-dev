import InitECandidate.Solver.WitnessRadix.LayoutProtected
import InitECandidate.Solver.WitnessRadix.OpenGraphSafety

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem protected_allocation_away (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (query : BitVec 64) (read : Protected layout allocated query) (different : query ≠ context.dest) :
    query ∉ (SplitCount.writes context).map Prod.fst := by
  have room := valid.room
  intro member
  rw [allocation_cells layout context allocated depth destination atLayout] at member
  simp only [allocationAddresses, List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with node | zero | one | dest | pendingStart | pendingCount | pendingNode
  · have away := protected_fresh layout valid allocated branchRoom query read 0 (by decide)
    exact away (by simpa [address] using node)
  · have away := protected_fresh layout valid allocated branchRoom query read 1 (by decide)
    exact away (by simpa [address] using zero)
  · have away := protected_fresh layout valid allocated branchRoom query read 2 (by decide)
    exact away (by simpa [address] using one)
  · exact different (dest.trans atLayout.destEq.symm)
  · have away := protected_buffer_away layout valid allocated branchRoom query read .primary (Or.inl rfl)
      (layout.count + depth) (by omega)
    exact away (by simpa only [address, Nat.mul_add] using pendingStart)
  · have away := protected_buffer_away layout valid allocated branchRoom query read .backup (Or.inr rfl)
      (layout.count + depth) (by omega)
    exact away (by simpa only [address, Nat.mul_add] using pendingCount)
  · exact protected_pending_vals layout valid allocated branchRoom query read depth stackRoom pendingNode

/-- Installed subtree reads survive a full split. The active pointer slot is
excluded by the frontier-safety invariant; every other write is excluded by
allocation geometry and the installed-branch count. -/
theorem split_graph_agreement {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (sliceFor : BitVec 64 → Graph.Slice) (immutable : Immutable source layout context.keyFor sliceFor)
    (tree : OpenGraph.Tree) (located : Located layout allocated tree)
    (safe : OpenGraph.SafeFrontier source layout.table layout.keys layout.vals tree)
    (active : ∃ expected, (context.dest, expected) ∈ OpenGraph.frontier tree) :
    ∀ query, OpenGraph.reads source layout.table layout.keys layout.vals tree query →
      source.memory query = (SplitCount.post source context).memory query := by
  have room := valid.room
  intro query read
  have protectedRead := located_reads source layout allocated valid context.keyFor sliceFor immutable tree located query read
  have different : query ≠ context.dest := by
    intro same
    subst query
    obtain ⟨expected, member⟩ := active
    exact safe _ member read
  apply Eq.symm
  apply SplitCount.post_away source context query
  · intro offset bound
    have rowEq : BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .primary (8 * (context.start + offset)) := by
      rw [atLayout.srcEq]
      exact row_cell layout .primary context.start offset
    rw [rowEq]
    exact protected_buffer_away layout valid allocated branchRoom query protectedRead .primary (Or.inl rfl)
      (context.start + offset) (by have := atLayout.interval; omega)
  · intro offset bound
    have rowEq : BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) =
        cell layout .backup (8 * (context.start + offset)) := by
      rw [atLayout.dstEq]
      exact row_cell layout .backup context.start offset
    rw [rowEq]
    exact protected_buffer_away layout valid allocated branchRoom query protectedRead .backup (Or.inr rfl)
      (context.start + offset) (by have := atLayout.interval; omega)
  · exact protected_allocation_away layout context allocated depth destination atLayout valid branchRoom stackRoom query protectedRead different

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.protected_allocation_away
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_graph_agreement
