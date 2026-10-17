import InitECandidate.Solver.WitnessRadix.PendingPush

namespace InitECandidate.Solver.WitnessRadix.PendingStack
open SplitScope

def OrderedFrom : Nat → List Task → Prop
  | _, [] => True
  | ending, task :: rest => ending ≤ task.start ∧ OrderedFrom (task.start + task.input.length) rest

theorem ordered_start (ending : Nat) (tasks : List Task) (ordered : OrderedFrom ending tasks)
    (task : Task) (member : task ∈ tasks) : ending ≤ task.start := by
  induction tasks generalizing ending with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with same | tail
      · subst task; exact ordered.1
      · have later := ih (head.start + head.input.length) ordered.2 tail
        have first := ordered.1
        omega

theorem right_task_end (context : SplitContext) :
    (rightTask context).start + (rightTask context).input.length = context.start + context.input.length := by
  have sum := ScatterProgram.zero_one_sum context.keyFor context.position context.input
  change zeroCount context + (rightTask context).input.length = context.input.length at sum
  change context.start + zeroCount context + (rightTask context).input.length = context.start + context.input.length
  omega

/-- Zero-first traversal retains increasing disjoint primary intervals:
the right child starts exactly where the active left child ends. -/
theorem ordered_push (context : SplitContext) (tasks : List Task)
    (ordered : OrderedFrom (context.start + context.input.length) tasks) :
    OrderedFrom (context.start + zeroCount context) (rightTask context :: tasks) := by
  refine ⟨Nat.le_refl _, ?_⟩
  rw [right_task_end]
  exact ordered

theorem ordered_pop (ending : Nat) (task : Task) (rest : List Task) (ordered : OrderedFrom ending (task :: rest)) :
    OrderedFrom (task.start + task.input.length) rest := ordered.2

end InitECandidate.Solver.WitnessRadix.PendingStack

#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.ordered_start
#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.ordered_push
