import InitECandidate.Solver.WitnessRadix.Visits

/-! A well-founded explicit agenda for the iterative builder. Connecting its
tasks to the actual array intervals/branch slots remains a memory invariant
proof, rather than an assumption hidden in these termination statements. -/
namespace InitECandidate.Solver.WitnessRadix

variable {Key Value : Type} [DecidableEq Key]

structure Task (Key Value : Type) where
  position : Nat
  fuel : Nat
  entries : List (Key × Value)

def taskWeight (task : Task Key Value) : Nat := (task.fuel + 1) * task.entries.length

def agendaWeight : List (Task Key Value) → Nat
  | [] => 0
  | task :: rest => taskWeight task + agendaWeight rest

def expand (bit : Key → Nat → Bool) (task : Task Key Value) : List (Task Key Value) :=
  match task.fuel with
  | 0 => []
  | fuel + 1 =>
      if task.entries.length ≤ 1 then [] else
        [⟨task.position + 1, fuel, task.entries.filter fun e => !bit e.1 task.position⟩,
         ⟨task.position + 1, fuel, task.entries.filter fun e => bit e.1 task.position⟩].filter
          (fun next => !next.entries.isEmpty)

theorem agendaWeight_append (left right : List (Task Key Value)) :
    agendaWeight (left ++ right) = agendaWeight left + agendaWeight right := by
  induction left with
  | nil => simp [agendaWeight]
  | cons task rest ih => simp [agendaWeight, ih, Nat.add_assoc]

theorem agendaWeight_filter (tasks : List (Task Key Value)) :
    agendaWeight (tasks.filter fun task => !task.entries.isEmpty) = agendaWeight tasks := by
  induction tasks with
  | nil => rfl
  | cons task rest ih =>
      cases task with
      | mk position fuel entries => cases entries <;> simp [agendaWeight, taskWeight, ih]

/-- A nonterminal split removes exactly one unit of remaining bit depth from
every record. Empty child intervals carry zero weight and are omitted. -/
theorem expanded_weight (bit : Key → Nat → Bool) (position fuel : Nat)
    (input : List (Key × Value)) (split : ¬ input.length ≤ 1) :
    agendaWeight (expand bit ⟨position, fuel + 1, input⟩) = (fuel + 1) * input.length := by
  simp only [expand, if_neg split]
  rw [agendaWeight_filter]
  simp only [agendaWeight, taskWeight, Nat.add_zero]
  rw [← Nat.mul_add, filter_length_sum (fun e => bit e.1 position) input]

theorem expand_decreases (bit : Key → Nat → Bool) (task : Task Key Value)
    (present : task.entries ≠ []) : agendaWeight (expand bit task) < taskWeight task := by
  cases task with
  | mk position fuel input =>
      have positive : 0 < input.length := List.length_pos_iff.mpr present
      cases fuel with
      | zero => simp [expand, agendaWeight, taskWeight, positive]
      | succ fuel =>
          by_cases terminal : input.length ≤ 1
          · simp only [expand, terminal, ↓reduceIte, agendaWeight, taskWeight]
            exact Nat.mul_pos (by omega) positive
          · rw [expanded_weight bit position fuel input terminal]
            change (fuel + 1) * input.length < (fuel + 2) * input.length
            exact Nat.mul_lt_mul_of_pos_right (by omega) positive

def AgendaValid (tasks : List (Task Key Value)) : Prop :=
  ∀ task ∈ tasks, task.entries ≠ []

theorem expand_valid (bit : Key → Nat → Bool) (task : Task Key Value) :
    AgendaValid (expand bit task) := by
  cases task with
  | mk position fuel input =>
      cases fuel with
      | zero => simp [expand, AgendaValid]
      | succ fuel =>
          by_cases terminal : input.length ≤ 1
          · simp [expand, terminal, AgendaValid]
          · intro next member empty
            simp only [expand, terminal, ↓reduceIte, List.mem_filter] at member
            have selected := member.2
            simp [empty] at selected

theorem next_valid (bit : Key → Nat → Bool) (task : Task Key Value) (rest : List (Task Key Value))
    (valid : AgendaValid (task :: rest)) : AgendaValid (expand bit task ++ rest) := by
  intro next member
  rcases List.mem_append.mp member with expanded | remaining
  · exact expand_valid bit task next expanded
  · exact valid next (List.mem_cons_of_mem task remaining)

def agendaRecords : List (Task Key Value) → Nat
  | [] => 0
  | task :: rest => task.entries.length + agendaRecords rest

theorem agendaRecords_append (left right : List (Task Key Value)) :
    agendaRecords (left ++ right) = agendaRecords left + agendaRecords right := by
  induction left with
  | nil => simp [agendaRecords]
  | cons task rest ih => simp [agendaRecords, ih, Nat.add_assoc]

theorem agendaRecords_filter (tasks : List (Task Key Value)) :
    agendaRecords (tasks.filter fun task => !task.entries.isEmpty) = agendaRecords tasks := by
  induction tasks with
  | nil => rfl
  | cons task rest ih =>
      cases task with
      | mk position fuel entries => cases entries <;> simp [agendaRecords, ih]

/-- Every pending task owns a nonempty disjoint record interval in the intended
memory invariant. The logical agenda never creates additional record mass. -/
theorem expand_records (bit : Key → Nat → Bool) (task : Task Key Value) :
    agendaRecords (expand bit task) ≤ task.entries.length := by
  cases task with
  | mk position fuel input =>
      cases fuel with
      | zero => simp [expand, agendaRecords]
      | succ fuel =>
          by_cases terminal : input.length ≤ 1
          · simp [expand, terminal, agendaRecords]
          · simp only [expand, terminal, ↓reduceIte]
            rw [agendaRecords_filter]
            simp only [agendaRecords, Nat.add_zero]
            rw [filter_length_sum (fun e => bit e.1 position) input]
            exact Nat.le_refl _

theorem agenda_length_le_records (tasks : List (Task Key Value)) (valid : AgendaValid tasks) :
    tasks.length ≤ agendaRecords tasks := by
  induction tasks with
  | nil => simp [agendaRecords]
  | cons task rest ih =>
      have nonempty := valid task (by simp)
      have positive := List.length_pos_iff.mpr nonempty
      have tail := ih (fun next member => valid next (List.mem_cons_of_mem task member))
      simp only [List.length_cons, agendaRecords]
      omega

/-- The current task and its pending siblings fit in N slots throughout any
logical agenda transition. The memory proof must additionally identify those
tasks with the implementation's three parallel suffix arrays. -/
theorem next_record_bound (bit : Key → Nat → Bool) (task : Task Key Value)
    (rest : List (Task Key Value)) (records : Nat)
    (budget : agendaRecords (task :: rest) ≤ records) :
    agendaRecords (expand bit task ++ rest) ≤ records := by
  rw [agendaRecords_append]
  have decreases := expand_records bit task
  simp only [agendaRecords] at budget
  omega

theorem next_slot_bound (bit : Key → Nat → Bool) (task : Task Key Value)
    (rest : List (Task Key Value)) (records : Nat)
    (valid : AgendaValid (task :: rest))
    (budget : agendaRecords (task :: rest) ≤ records) :
    (expand bit task ++ rest).length ≤ records :=
  Nat.le_trans (agenda_length_le_records _ (next_valid bit task rest valid))
    (next_record_bound bit task rest records budget)

inductive AgendaRun (bit : Key → Nat → Bool) : List (Task Key Value) → Nat → Prop
  | done : AgendaRun bit [] 0
  | step {task rest count} (present : task.entries ≠ [])
      (next : AgendaRun bit (expand bit task ++ rest) count) :
      AgendaRun bit (task :: rest) (count + 1)

theorem agenda_terminates (bit : Key → Nat → Bool) (tasks : List (Task Key Value))
    (valid : AgendaValid tasks) : ∃ count, AgendaRun bit tasks count := by
  have general : ∀ bound (agenda : List (Task Key Value)), agendaWeight agenda = bound →
      AgendaValid agenda → ∃ count, AgendaRun bit agenda count := by
    intro bound
    induction bound using Nat.strongRecOn with
    | ind bound ih =>
        intro agenda weight good
        cases agenda with
        | nil => exact ⟨0, .done⟩
        | cons task rest =>
            have present := good task (by simp)
            have smaller : agendaWeight (expand bit task ++ rest) < bound := by
              rw [agendaWeight_append]
              have decreases := expand_decreases bit task present
              simp only [agendaWeight] at weight
              omega
            obtain ⟨count, execution⟩ := ih _ smaller _ rfl (next_valid bit task rest good)
            exact ⟨count + 1, .step present execution⟩
  exact general (agendaWeight tasks) tasks rfl valid

theorem agenda_steps_bound (bit : Key → Nat → Bool) {tasks : List (Task Key Value)} {count : Nat}
    (run : AgendaRun bit tasks count) : count ≤ agendaWeight tasks := by
  induction run with
  | done => simp [agendaWeight]
  | @step task rest count present run ih =>
      have smaller := expand_decreases bit task present
      rw [agendaWeight_append] at ih
      simp only [agendaWeight]
      omega

/-- No external termination hypothesis: every nonempty record list completes
the logical iterative agenda within 257N outer iterations. -/
theorem hash_agenda_bound (input : List (BitVec 256 × Value)) (present : input ≠ []) :
    ∃ count, count ≤ 257 * input.length ∧
      AgendaRun BitVec.getLsbD [⟨0, 256, input⟩] count := by
  have valid : AgendaValid [({ position := 0, fuel := 256, entries := input } : Task (BitVec 256) Value)] := by
    intro task member
    simp only [List.mem_singleton] at member
    subst task
    exact present
  obtain ⟨count, run⟩ := agenda_terminates BitVec.getLsbD _ valid
  refine ⟨count, ?_, run⟩
  simpa [agendaWeight, taskWeight] using agenda_steps_bound BitVec.getLsbD run

end InitECandidate.Solver.WitnessRadix

#print axioms InitECandidate.Solver.WitnessRadix.expand_decreases
#print axioms InitECandidate.Solver.WitnessRadix.agenda_terminates
#print axioms InitECandidate.Solver.WitnessRadix.hash_agenda_bound
#print axioms InitECandidate.Solver.WitnessRadix.next_record_bound
#print axioms InitECandidate.Solver.WitnessRadix.next_slot_bound
