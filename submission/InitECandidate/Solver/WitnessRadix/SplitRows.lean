import InitECandidate.Solver.WitnessRadix.SplitGraph
import InitECandidate.Solver.WitnessRadix.RowsFrame

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem sorted_primary_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (fits : context.start + context.input.length ≤ context.limit)
    (allocation : context.src.toNat + 8 * context.limit < 2 ^ 64)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input) :
    BuildCopy.Rows
      (SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input)
      source.memaddrs context.src (BitVec.ofNat 64 context.start) 0
      (ScatterProgram.partition context.keyFor context.position context.input) := by
  have small : context.start < 2 ^ 64 := by omega
  apply BuildCopy.copied_rows
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt small, ScatterProgram.partition_length]
    omega
  · intro offset bound
    have mapped := BuildCopy.rows_mapped _ _ _ _ _ _ rows offset
      (by simpa only [ScatterProgram.partition_length] using bound)
    exact mapped

/-- Full split execution leaves the exact stable partition readable in the
primary interval after all seven allocation/pending stores. -/
theorem primary_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (fits : context.start + context.input.length ≤ context.limit)
    (allocation : context.src.toNat + 8 * context.limit < 2 ^ 64)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (away : ∀ offset < context.input.length,
      BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) ∉ (writes context).map Prod.fst) :
    BuildCopy.Rows (post source context).memory (post source context).memaddrs
      context.src (BitVec.ofNat 64 context.start) 0
      (ScatterProgram.partition context.keyFor context.position context.input) := by
  apply BuildCopy.rows_of_agreement _ _ source.memaddrs _ _ _ _ _ (sorted_primary_rows source context fits allocation rows)
  intro offset bound
  have away' := away offset (by simpa only [ScatterProgram.partition_length] using bound)
  change (SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input)
    (BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 (0 + offset))) =
    SplitProgram.branchMemory
      (SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input)
      context.node context.depth (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
      (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position) context.dest
      context.pendingStart context.pendingCount context.pendingNode
      (BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 (0 + offset)))
  simpa only [Nat.zero_add] using
    (SplitProgram.branchMemory_frame
      (SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input)
      context.node context.depth (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
      (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position) context.dest
      context.pendingStart context.pendingCount context.pendingNode _ away').symm

/-- The two child tasks read their own adjacent primary intervals. -/
theorem child_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (fits : context.start + context.input.length ≤ context.limit)
    (allocation : context.src.toNat + 8 * context.limit < 2 ^ 64)
    (rows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (away : ∀ offset < context.input.length,
      BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset) ∉ (writes context).map Prod.fst) :
    BuildCopy.Rows (post source context).memory (post source context).memaddrs
      context.src (BitVec.ofNat 64 context.start) 0
      (context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal) ∧
    BuildCopy.Rows (post source context).memory (post source context).memaddrs
      context.src (BitVec.ofNat 64 (context.start + zeroCount context)) 0
      (context.input.filter (ScatterProgram.keep context.keyFor context.position)) := by
  have partitionRows := primary_rows source context fits allocation rows away
  rw [ScatterProgram.partition, BuildCopy.rows_append] at partitionRows
  refine ⟨partitionRows.1, ?_⟩
  rw [BuildCopy.rows_start_shift]
  have right := partitionRows.2
  rw [BuildCopy.rows_start_shift] at right
  simpa only [Nat.add_zero, Nat.zero_add, zeroCount, ScatterProgram.zeros] using right

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.primary_rows
#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.child_rows
