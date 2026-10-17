import InitECandidate.Solver.WitnessRadix.LayoutContext
import InitECandidate.Solver.WitnessRadix.PendingStack

namespace InitECandidate.Solver.WitnessRadix.BackingLayout

def ParentsWithin (layout : Layout) (allocated : Nat) (tasks : List PendingStack.Task) : Prop :=
  ∀ task ∈ tasks, ∃ index < allocated, task.parent = branchAddress layout.keys layout.count index

def StackReadZone (layout : Layout) (allocated depth : Nat) (query : BitVec 64) : Prop :=
  (∃ pool, (pool = .primary ∨ pool = .backup ∨ pool = .vals) ∧ ∃ index < depth,
    query = cell layout pool (8 * layout.count + 8 * index)) ∨
  ∃ index < allocated, query = cell layout .keys (32 * layout.count + 24 * index)

theorem pending_cell (layout : Layout) (pool : Pool) (depth : Nat) :
    cell layout pool (8 * layout.count) + (BitVec.ofNat 64 (depth + 1) - 1#64) * 8#64 =
      cell layout pool (8 * layout.count + 8 * depth) := by
  rw [BitVec.ofNat_add, BitVec.add_sub_cancel]
  simp only [cell, byteAddress, BitVec.ofNat_add, BitVec.ofNat_mul, Nat.mul_comm, BitVec.add_assoc]

theorem stack_zone_mono (layout : Layout) (allocated before after : Nat) (increase : before ≤ after) (query : BitVec 64)
    (zone : StackReadZone layout allocated before query) : StackReadZone layout allocated after query := by
  rcases zone with suffix | parent
  · obtain ⟨pool, selected, index, bound, value⟩ := suffix
    exact Or.inl ⟨pool, selected, index, by omega, value⟩
  · exact Or.inr parent

/-- Every actual pending-pop read is a lower stack cell or an installed
parent bit word. No assumption about a successful pop is needed. -/
theorem pending_read_zone (layout : Layout) (allocated : Nat) (tasks : List PendingStack.Task)
    (parents : ParentsWithin layout allocated tasks) (query : BitVec 64)
    (read : PendingStack.reads (cell layout .primary (8 * layout.count)) (cell layout .backup (8 * layout.count))
      (cell layout .vals (8 * layout.count)) tasks query) : StackReadZone layout allocated tasks.length query := by
  induction tasks with
  | nil => exact False.elim read
  | cons task rest ih =>
      rcases read with start | count | node | parent | tail
      · exact Or.inl ⟨.primary, Or.inl rfl, rest.length, by simp,
          start.trans (pending_cell layout .primary rest.length)⟩
      · exact Or.inl ⟨.backup, Or.inr (Or.inl rfl), rest.length, by simp,
          count.trans (pending_cell layout .backup rest.length)⟩
      · exact Or.inl ⟨.vals, Or.inr (Or.inr rfl), rest.length, by simp,
          node.trans (pending_cell layout .vals rest.length)⟩
      · obtain ⟨index, bound, address⟩ := parents task (by simp)
        exact Or.inr ⟨index, bound, parent.trans address⟩
      · exact stack_zone_mono layout allocated rest.length (task :: rest).length (by simp) query
          (ih (fun next member => parents next (List.mem_cons_of_mem task member)) tail)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.pending_cell
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.pending_read_zone
