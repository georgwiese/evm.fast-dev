import InitECandidate.Solver.WitnessRadix.LayoutContext
import InitECandidate.Solver.WitnessRadix.PendingIntervals

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

structure ValidTask (layout : Layout) (task : PendingStack.Task) : Prop where
  interval : task.start + task.input.length ≤ layout.count
  present : task.input ≠ []
  position : task.parentPosition < 256
  ordinals : ∀ ordinal ∈ task.input, ordinal.toNat < layout.count

def ValidPending (layout : Layout) (tasks : List PendingStack.Task) : Prop := ∀ task ∈ tasks, ValidTask layout task

theorem valid_right_task (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (inside : context.position < 256)
    (splitOne : zeroCount context < context.input.length) : ValidTask layout (PendingStack.rightTask context) := by
  refine ⟨?_, ?_, inside, ?_⟩
  · rw [PendingStack.right_task_end]
    exact atLayout.interval
  · have length := PendingStack.right_length context
    have positive : 0 < (PendingStack.rightTask context).input.length := by omega
    exact List.length_pos_iff.mp positive
  · intro ordinal member
    exact atLayout.ordinals ordinal (List.mem_of_mem_filter member)

theorem valid_pending_push (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (inside : context.position < 256)
    (splitOne : zeroCount context < context.input.length) (tasks : List PendingStack.Task)
    (valid : ValidPending layout tasks) : ValidPending layout (PendingStack.rightTask context :: tasks) := by
  intro task member
  rcases List.mem_cons.mp member with head | tail
  · subst task; exact valid_right_task layout context allocated depth destination atLayout inside splitOne
  · exact valid task tail

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.valid_right_task
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.valid_pending_push
