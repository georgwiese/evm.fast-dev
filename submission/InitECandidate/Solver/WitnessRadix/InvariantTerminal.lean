import InitECandidate.Solver.WitnessRadix.InvariantClock
import InitECandidate.Solver.WitnessRadix.AgendaBudget
import InitECandidate.Solver.WitnessRadix.OpenGraphSelect
import InitECandidate.Solver.WitnessRadix.LayoutLeafFrontier
import InitECandidate.Solver.WitnessRadix.LayoutLeafRows

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

def resumePost {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (task : PendingStack.Task) (ordinal : Nat) : PanSemStateFiniteExact 64 F :=
  PopProgram.popPost (OpenGraph.leafPost source context.dest ordinal) context.depth
    (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition)

/-- The actual terminal body fills its leaf and resumes the saved sibling,
re-establishing every component of the full construction invariant. -/
theorem invariant_terminal_continue {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (valid : Valid layout)
    (sliceFor : BitVec 64 → Graph.Slice) (expectedTree : Graph.Tree) (allocated completed depth : Nat)
    (context : SplitContext) (destination : Address) (task : PendingStack.Task) (rest : List PendingStack.Task) (graph : OpenGraph.Tree)
    (inv : Invariant source layout sliceFor expectedTree allocated completed depth context destination (task :: rest) graph)
    (stop : context.input.length = 1 ∨ context.position = 256) (ordinal : BitVec 64) (last : context.input.getLast? = some ordinal) :
    ∃ nextGraph parent,
      evaluateHOLFiniteState source BuildEntry.mainBody = (some .continue, resumePost source context task ordinal.toNat) ∧
      Invariant (resumePost source context task ordinal.toNat) layout sliceFor expectedTree allocated (completed + 1) rest.length
        (resumeContext context task rest.length) (resumeDestination layout parent) rest nextGraph := by
  have branchRoom := invariant_branch_room source layout sliceFor expectedTree allocated completed depth context destination (task :: rest) graph inv
  have stackRoom := invariant_stack_room source layout sliceFor expectedTree allocated completed depth context destination (task :: rest) graph inv
  have ordinalBound := inv.atLayout.ordinals ordinal (List.mem_of_getLast? last)
  have treeEq : currentTree context sliceFor =
      .leaf (context.keyFor (BitVec.ofNat 64 ordinal.toNat)) (sliceFor (BitVec.ofNat 64 ordinal.toNat)) := by
    have model := OrdinalTree.terminal context.keyFor sliceFor context.position context.input ordinal last stop.symm
    simpa [currentTree] using model
  obtain ⟨nextGraph, step⟩ := OpenGraph.fill_first_exists graph context.dest (currentTree context sliceFor)
    (completedLeaf context sliceFor ordinal.toNat) ((task :: rest).map (savedHole context.keyFor sliceFor)) inv.aligned
  have leafStep : OpenGraph.FillFirst context.dest
      (.leaf (context.keyFor (BitVec.ofNat 64 ordinal.toNat)) (sliceFor (BitVec.ofNat 64 ordinal.toNat)))
      (completedLeaf context sliceFor ordinal.toNat) graph nextGraph := by
    rw [← treeEq]
    exact step
  have leafRep := fill_leaf_graph source layout context allocated depth destination inv.atLayout valid inv.mapped branchRoom
    sliceFor inv.immutable ordinal.toNat ordinalBound graph nextGraph leafStep inv.represented inv.safe
  have leafFrontier := leaf_frontier_update source layout context allocated depth destination inv.atLayout valid branchRoom
    sliceFor inv.immutable ordinal.toNat ordinalBound graph nextGraph leafStep inv.located inv.safe inv.distinct
  have remaining := leaf_remaining context sliceFor (task :: rest) graph nextGraph ordinal.toNat inv.aligned step
  obtain ⟨parent, parentBound, parentEq⟩ := inv.parents task (by simp)
  have taskValid := inv.pendingValid task (by simp)
  let leafState := OpenGraph.leafPost source context.dest ordinal.toNat
  let target := resumePost source context task ordinal.toNat
  have leafImmutable := leaf_immutable source layout context allocated depth destination inv.atLayout valid branchRoom sliceFor inv.immutable ordinal.toNat
  have leafRows := leaf_pending_rows source layout context allocated depth destination inv.atLayout valid branchRoom stackRoom ordinal.toNat
    (task :: rest) (fun saved member => (inv.pendingValid saved member).interval) inv.pendingRows
  have headRows := leafRows task (by simp)
  rw [← inv.atLayout.srcEq] at headRows
  have depthWord : context.depth = BitVec.ofNat 64 (rest.length + 1) := by rw [inv.atLayout.depthEq, ← inv.length]; rfl
  have leafLocals := SplitCount.task_locals_of_lookup source leafState context (by intros; rfl) inv.locals
  have leafStack := PendingStack.represents_of_agreement source leafState rfl _ _ _ (task :: rest)
    (leaf_pending_agreement source layout context allocated depth destination inv.atLayout valid branchRoom stackRoom
      (task :: rest) inv.length inv.parents ordinal.toNat) inv.stack
  have tailStack := PendingStack.pop_tail leafState context.pendingStart context.pendingCount context.pendingNode task rest leafStack
  have execution := terminal_body_continue source layout context allocated depth destination inv.atLayout valid inv.mapped branchRoom stackRoom
    inv.locals inv.rows stop ordinal last task rest inv.length inv.parents inv.stack
  refine ⟨nextGraph, parent, execution, ?_⟩
  refine ⟨inv.mapped,
    immutable_of_agreement leafState target layout valid context.keyFor sliceFor rfl rfl (by intros; rfl) leafImmutable,
    resume_layout layout context allocated depth destination inv.atLayout task rest.length parent taskValid parentBound parentEq,
    resume_locals leafState context task rest.length depthWord leafLocals, headRows, taskValid.present,
    (by change task.parentPosition + 1 ≤ 256; have := taskValid.position; omega), rfl,
    (fun saved member => inv.pendingValid saved (List.mem_cons_of_mem task member)),
    (fun saved member => inv.parents saved (List.mem_cons_of_mem task member)), ?_,
    (fun saved member => leafRows saved (List.mem_cons_of_mem task member)), inv.ordered.2,
    OpenGraph.represents_of_agreement leafState target rfl rfl layout.table layout.keys layout.vals nextGraph (by intros; rfl) leafRep.1,
    leafFrontier.2.1, ?_, leafFrontier.2.2, pop_aligned context sliceFor task rest nextGraph remaining,
    leafRep.2.trans inv.expected,
    (OpenGraph.replacement_slot (OpenGraph.fill_replaces step) rfl).trans inv.root,
    terminal_agenda_budget layout context task rest completed allocated inv.budget⟩
  · simpa only [resumePost, resumeContext, leafState, List.length_cons, depthWord] using tailStack
  · intro entry member read
    exact leafFrontier.1 entry member
      ((OpenGraph.reads_stable leafState target layout.table layout.keys layout.vals nextGraph (by intros; rfl) entry.1).mpr read)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.invariant_terminal_continue
