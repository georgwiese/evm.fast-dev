import InitECandidate.Solver.WitnessRadix.Worklist
import InitECandidate.Solver.WitnessRadix.ByteKeys

namespace InitECandidate.Solver.WitnessRadix
variable {Key Value : Type} [DecidableEq Key]

/-- Upper source-clock price of one actual outer case: terminal one clock,
otherwise count plus at most scatter/copy and the outer while step. -/
def taskCost (task : Task Key Value) : Nat :=
  if task.fuel = 0 ∨ task.entries.length ≤ 1 then 1 else 3 * task.entries.length + 1

theorem task_cost_potential (bit : Key → Nat → Bool) (task : Task Key Value)
    (present : task.entries ≠ []) :
    taskCost task + 4 * agendaWeight (expand bit task) ≤ 4 * taskWeight task := by
  have positive : 0 < task.entries.length := List.length_pos_iff.mpr present
  cases task with
  | mk position fuel input =>
      change 0 < input.length at positive
      cases fuel with
      | zero => simp [taskCost, expand, agendaWeight, taskWeight]; omega
      | succ fuel =>
          by_cases terminal : input.length ≤ 1
          · simp only [taskCost, Nat.succ_ne_zero, false_or, if_pos terminal,
              expand, agendaWeight, taskWeight, Nat.mul_zero, Nat.add_zero]
            have mul : input.length ≤ (fuel + 1 + 1) * input.length := Nat.le_mul_of_pos_left _ (by omega)
            omega
          · rw [expanded_weight bit position fuel input terminal]
            simp only [taskCost, Nat.succ_ne_zero, false_or, if_neg terminal, taskWeight]
            simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
            omega

inductive AgendaCostRun (bit : Key → Nat → Bool) : List (Task Key Value) → Nat → Prop
  | done : AgendaCostRun bit [] 0
  | step {task rest cost} (present : task.entries ≠ [])
      (next : AgendaCostRun bit (expand bit task ++ rest) cost) :
      AgendaCostRun bit (task :: rest) (taskCost task + cost)

theorem agenda_cost_bound (bit : Key → Nat → Bool) {tasks : List (Task Key Value)} {cost : Nat}
    (run : AgendaCostRun bit tasks cost) : cost ≤ 4 * agendaWeight tasks := by
  induction run with
  | done => simp [agendaWeight]
  | @step task rest cost present next ih =>
      have stepBound := task_cost_potential bit task present
      rw [agendaWeight_append, Nat.mul_add] at ih
      simp only [agendaWeight, Nat.mul_add]
      omega

theorem agenda_cost_exists (bit : Key → Nat → Bool) (tasks : List (Task Key Value))
    (valid : AgendaValid tasks) : ∃ cost, AgendaCostRun bit tasks cost ∧ cost ≤ 4 * agendaWeight tasks := by
  obtain ⟨count, run⟩ := agenda_terminates bit tasks valid
  have costed : ∃ cost, AgendaCostRun bit tasks cost := by
    clear valid
    induction run with
    | done => exact ⟨0, .done⟩
    | step present next ih =>
        obtain ⟨cost, costRun⟩ := ih
        exact ⟨_, .step present costRun⟩
  obtain ⟨cost, costRun⟩ := costed
  exact ⟨cost, costRun, agenda_cost_bound bit costRun⟩

/-- A conservative linear price matching all proved actual outer cases.
The memory/agenda refinement must still connect an execution to this run. -/
theorem byte_agenda_cost (keyFor : BitVec 64 → ByteKeys.Key) (input : List (BitVec 64 × Value))
    (present : input ≠ []) :
    ∃ cost, AgendaCostRun (fun ordinal position => ByteKeys.bit (keyFor ordinal) position)
      [⟨0, 256, input⟩] cost ∧ cost ≤ 1028 * input.length := by
  have valid : AgendaValid [({ position := 0, fuel := 256, entries := input } : Task (BitVec 64) Value)] := by
    intro task member
    simp only [List.mem_singleton] at member
    subst task
    exact present
  obtain ⟨cost, run, bound⟩ := agenda_cost_exists (fun ordinal position => ByteKeys.bit (keyFor ordinal) position) _ valid
  refine ⟨cost, run, ?_⟩
  simpa only [agendaWeight, taskWeight, Nat.add_zero, ← Nat.mul_assoc] using bound

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.task_cost_potential
#print axioms InitECandidate.Solver.WitnessRadix.agenda_cost_bound
#print axioms InitECandidate.Solver.WitnessRadix.byte_agenda_cost
