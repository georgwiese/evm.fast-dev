import InitECandidate.Solver.WitnessRadix.Worklist

namespace InitECandidate.Solver.WitnessRadix
variable {Key Value : Type} [DecidableEq Key]

/-- Cumulative branch/leaf accounting for a partially constructed full tree.
Each frontier task owns at least one input record. -/
structure FrontierBudget (records completed branches : Nat) (tasks : List (Task Key Value)) : Prop where
  valid : AgendaValid tasks
  mass : completed + agendaRecords tasks ≤ records
  balance : branches + 1 = completed + tasks.length

theorem frontier_branch_room {records completed branches : Nat} {tasks : List (Task Key Value)}
    (budget : FrontierBudget records completed branches tasks) : branches < records := by
  have slots := agenda_length_le_records tasks budget.valid
  have mass := budget.mass
  have balance := budget.balance
  omega

theorem initial_frontier_budget (input : List (Key × Value)) (present : input ≠ []) (position fuel : Nat) :
    FrontierBudget input.length 0 0 [⟨position, fuel, input⟩] := by
  refine ⟨?_, ?_, ?_⟩
  · intro task member
    simp only [List.mem_singleton] at member
    subst task
    exact present
  · simp [agendaRecords]
  · rfl

/-- Completing a bucket adds one leaf, even when it discards duplicate keys. -/
theorem terminal_frontier_budget {records completed branches : Nat} {task : Task Key Value} {rest : List (Task Key Value)}
    (budget : FrontierBudget records completed branches (task :: rest)) :
    FrontierBudget records (completed + 1) branches rest := by
  have present := budget.valid task (by simp)
  have positive := List.length_pos_iff.mpr present
  refine ⟨fun next member => budget.valid next (List.mem_cons_of_mem task member), ?_, ?_⟩
  · have mass := budget.mass
    simp only [agendaRecords] at mass
    omega
  · have balance := budget.balance
    simp only [List.length_cons] at balance
    omega

/-- A unary level changes no branch/leaf/record counts. -/
theorem unary_frontier_budget {records completed branches : Nat} {task next : Task Key Value} {rest : List (Task Key Value)}
    (budget : FrontierBudget records completed branches (task :: rest))
    (same : next.entries = task.entries) : FrontierBudget records completed branches (next :: rest) := by
  refine ⟨?_, ?_, ?_⟩
  · intro candidate member
    rcases List.mem_cons.mp member with head | tail
    · subst candidate
      rw [same]
      exact budget.valid task (by simp)
    · exact budget.valid candidate (List.mem_cons_of_mem task tail)
  · simpa only [agendaRecords, same] using budget.mass
  · simpa only [List.length_cons] using budget.balance

/-- A genuine split installs one branch and replaces its hole by two
nonempty record partitions, preserving the cumulative allocation budget. -/
theorem split_frontier_budget {records completed branches : Nat} {task zero one : Task Key Value} {rest : List (Task Key Value)}
    (budget : FrontierBudget records completed branches (task :: rest))
    (zeroPresent : zero.entries ≠ []) (onePresent : one.entries ≠ [])
    (partition : zero.entries.length + one.entries.length = task.entries.length) :
    FrontierBudget records completed (branches + 1) (zero :: one :: rest) := by
  refine ⟨?_, ?_, ?_⟩
  · intro candidate member
    rcases List.mem_cons.mp member with head | tail
    · subst candidate; exact zeroPresent
    · rcases List.mem_cons.mp tail with head | tail
      · subst candidate; exact onePresent
      · exact budget.valid candidate (List.mem_cons_of_mem task tail)
  · have mass := budget.mass
    simp only [agendaRecords] at mass ⊢
    omega
  · have balance := budget.balance
    simp only [List.length_cons] at balance ⊢
    omega

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.frontier_branch_room
#print axioms InitECandidate.Solver.WitnessRadix.terminal_frontier_budget
#print axioms InitECandidate.Solver.WitnessRadix.split_frontier_budget
