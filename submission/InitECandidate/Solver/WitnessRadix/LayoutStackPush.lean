import InitECandidate.Solver.WitnessRadix.LayoutStackFrame
import InitECandidate.Solver.WitnessRadix.LayoutSplitMemory
import InitECandidate.Solver.WitnessRadix.PendingPush

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

/-- A complete actual split prepends the right task to the physical suffix
stack, with all old stack cells protected by the common geometry invariant. -/
theorem split_stack_represents {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout) (mapped : Mapped source layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (tasks : List PendingStack.Task) (length : tasks.length = depth) (parents : ParentsWithin layout allocated tasks)
    (rep : PendingStack.Represents source context.pendingStart context.pendingCount context.pendingNode tasks) :
    PendingStack.Represents (SplitCount.post source context) context.pendingStart context.pendingCount context.pendingNode
      (PendingStack.rightTask context :: tasks) := by
  have depthEq : context.depth = BitVec.ofNat 64 tasks.length := by rw [length]; exact atLayout.depthEq
  have small : context.input.length < 2 ^ 64 := by
    have countBound := count_small layout valid
    have fits := atLayout.interval
    omega
  have head := PendingStack.push_head_cells source context tasks depthEq small
    (allocation_distinct layout context allocated depth destination atLayout valid branchRoom stackRoom)
    (context_allocation_mapped source layout context allocated depth destination atLayout valid mapped branchRoom stackRoom)
  refine ⟨head, ?_⟩
  exact PendingStack.represents_of_agreement source (SplitCount.post source context) rfl _ _ _ tasks
    (split_pending_agreement source layout context allocated depth destination atLayout valid branchRoom stackRoom tasks length parents) rep

theorem pushed_parents (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (tasks : List PendingStack.Task)
    (parents : ParentsWithin layout allocated tasks) :
    ParentsWithin layout (allocated + 1) (PendingStack.rightTask context :: tasks) := by
  intro task member
  rcases List.mem_cons.mp member with head | tail
  · subst task
    exact ⟨allocated, by omega, atLayout.nodeEq⟩
  · obtain ⟨index, bound, word⟩ := parents task tail
    exact ⟨index, by omega, word⟩

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_stack_represents
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.pushed_parents
