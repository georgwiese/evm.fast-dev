import InitECandidate.Solver.WitnessRadix.ConstructionInvariant

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

def unaryContext (context : SplitContext) : SplitContext := { context with position := context.position + 1 }

theorem split_agenda_budget (layout : Layout) (context : SplitContext) (tasks : List PendingStack.Task) (completed allocated : Nat)
    (budget : FrontierBudget layout.count completed allocated (agenda context tasks))
    (splitZero : 0 < zeroCount context) (splitOne : zeroCount context < context.input.length) :
    FrontierBudget layout.count completed (allocated + 1)
      (agenda (SplitCount.leftContext context) (PendingStack.rightTask context :: tasks)) := by
  have zeroLength : (activeAgendaTask (SplitCount.leftContext context)).entries.length = zeroCount context := by
    simp only [activeAgendaTask, SplitCount.leftContext, List.length_map, zeroCount, ScatterProgram.zeros]
  have oneLength : (savedAgendaTask (PendingStack.rightTask context)).entries.length =
      context.input.length - zeroCount context := by
    simpa only [savedAgendaTask, List.length_map] using PendingStack.right_length context
  have zeroPresent : (activeAgendaTask (SplitCount.leftContext context)).entries ≠ [] := by
    intro empty
    rw [empty] at zeroLength
    change 0 = zeroCount context at zeroLength
    omega
  have onePresent : (savedAgendaTask (PendingStack.rightTask context)).entries ≠ [] := by
    intro empty
    rw [empty] at oneLength
    change 0 = context.input.length - zeroCount context at oneLength
    omega
  apply split_frontier_budget budget zeroPresent onePresent
  rw [zeroLength, oneLength]
  simp only [activeAgendaTask, List.length_map]
  omega

theorem terminal_agenda_budget (layout : Layout) (context : SplitContext) (task : PendingStack.Task)
    (rest : List PendingStack.Task) (completed allocated : Nat)
    (budget : FrontierBudget layout.count completed allocated (agenda context (task :: rest))) :
    FrontierBudget layout.count (completed + 1) allocated (agenda (resumeContext context task rest.length) rest) :=
  terminal_frontier_budget budget

theorem unary_agenda_budget (layout : Layout) (context : SplitContext) (tasks : List PendingStack.Task) (completed allocated : Nat)
    (budget : FrontierBudget layout.count completed allocated (agenda context tasks)) :
    FrontierBudget layout.count completed allocated (agenda (unaryContext context) tasks) :=
  unary_frontier_budget budget rfl

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_agenda_budget
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_agenda_budget
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.unary_agenda_budget
