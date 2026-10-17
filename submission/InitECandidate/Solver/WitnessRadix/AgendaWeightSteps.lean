import InitECandidate.Solver.WitnessRadix.AgendaBudget

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

theorem weight_ge_length (context : SplitContext) (tasks : List PendingStack.Task) :
    context.input.length ≤ agendaWeight (agenda context tasks) := by
  have product : context.input.length ≤ (256 - context.position + 1) * context.input.length :=
    Nat.le_mul_of_pos_left _ (by omega)
  simpa only [agenda, agendaWeight, activeAgendaTask, taskWeight, List.length_map] using
    Nat.le_add_right_of_le product

theorem unary_weight (context : SplitContext) (tasks : List PendingStack.Task) (inside : context.position < 256) :
    agendaWeight (agenda context tasks) = agendaWeight (agenda (unaryContext context) tasks) + context.input.length := by
  have fuel : 256 - context.position = (256 - (context.position + 1)) + 1 := by omega
  simp only [agenda, agendaWeight, activeAgendaTask, unaryContext, taskWeight, List.length_map]
  rw [fuel]
  simp only [Nat.add_mul, Nat.one_mul]
  omega

theorem split_weight (context : SplitContext) (tasks : List PendingStack.Task) (inside : context.position < 256) :
    agendaWeight (agenda context tasks) =
      agendaWeight (agenda (SplitCount.leftContext context) (PendingStack.rightTask context :: tasks)) + context.input.length := by
  let unitWeight := 256 - (context.position + 1) + 1
  let zero := (context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal).length
  let one := (context.input.filter (ScatterProgram.keep context.keyFor context.position)).length
  let tail := agendaWeight (tasks.map savedAgendaTask)
  have sum : zero + one = context.input.length := ScatterProgram.zero_one_sum context.keyFor context.position context.input
  have fuel : 256 - context.position = (256 - (context.position + 1)) + 1 := by omega
  have priced : (256 - context.position + 1) * context.input.length = unitWeight * context.input.length + context.input.length := by
    rw [fuel]
    change ((256 - (context.position + 1) + 1) + 1) * context.input.length = _
    rw [Nat.add_mul]
    simp only [Nat.one_mul, unitWeight]
  have joined : unitWeight * zero + (unitWeight * one + tail) = unitWeight * context.input.length + tail := by
    rw [← Nat.add_assoc, ← Nat.mul_add, sum]
  simp only [agenda, List.map_cons, agendaWeight, activeAgendaTask, savedAgendaTask, SplitCount.leftContext,
    PendingStack.rightTask, taskWeight, List.length_map]
  change (256 - context.position + 1) * context.input.length + tail =
    (unitWeight * zero + (unitWeight * one + tail)) + context.input.length
  rw [priced, joined]
  omega

theorem terminal_weight (context : SplitContext) (task : PendingStack.Task) (rest : List PendingStack.Task) :
    agendaWeight (agenda context (task :: rest)) =
      (256 - context.position + 1) * context.input.length +
        agendaWeight (agenda (resumeContext context task rest.length) rest) := by
  simp only [agenda, agendaWeight, List.map_cons, activeAgendaTask, savedAgendaTask, resumeContext, taskWeight, List.length_map]

theorem unary_price (context : SplitContext) (tasks : List PendingStack.Task) (inside : context.position < 256)
    (present : 0 < context.input.length) :
    context.input.length + 1 + 4 * agendaWeight (agenda (unaryContext context) tasks) ≤ 4 * agendaWeight (agenda context tasks) := by
  rw [unary_weight context tasks inside, Nat.mul_add]
  omega

theorem split_price (context : SplitContext) (tasks : List PendingStack.Task) (inside : context.position < 256)
    (present : 0 < context.input.length) :
    3 * context.input.length + 1 + 4 * agendaWeight (agenda (SplitCount.leftContext context) (PendingStack.rightTask context :: tasks)) ≤
      4 * agendaWeight (agenda context tasks) := by
  rw [split_weight context tasks inside, Nat.mul_add]
  omega

theorem terminal_price (context : SplitContext) (task : PendingStack.Task) (rest : List PendingStack.Task)
    (present : 0 < context.input.length) :
    1 + 4 * agendaWeight (agenda (resumeContext context task rest.length) rest) ≤ 4 * agendaWeight (agenda context (task :: rest)) := by
  have product : 1 ≤ (256 - context.position + 1) * context.input.length :=
    Nat.mul_pos (by omega) present
  rw [terminal_weight, Nat.mul_add]
  omega

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.unary_weight
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_weight
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_price
