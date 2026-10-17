import InitECandidate.Solver.WitnessRadix.PendingStack
import InitECandidate.Solver.WitnessRadix.SplitGraph

namespace InitECandidate.Solver.WitnessRadix.PendingStack
open Flapjack PanSemStateFiniteExact
open SplitScope

def rightTask (context : SplitContext) : Task :=
  ⟨context.start + zeroCount context,
    context.input.filter (ScatterProgram.keep context.keyFor context.position), context.node, context.position⟩

theorem right_length (context : SplitContext) :
    (rightTask context).input.length = context.input.length - zeroCount context := by
  have sum := ScatterProgram.zero_one_sum context.keyFor context.position context.input
  change zeroCount context + (rightTask context).input.length = context.input.length at sum
  omega

theorem push_head_cells {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (tasks : List Task)
    (depth : context.depth = BitVec.ofNat 64 tasks.length)
    (small : context.input.length < 2 ^ 64)
    (distinct : ((SplitCount.writes context).map Prod.fst).Nodup)
    (mapped : SplitProgram.Mapped source context.node context.depth context.dest
      context.pendingStart context.pendingCount context.pendingNode) :
    PopProgram.Cells (SplitCount.post source context) (BitVec.ofNat 64 ((rightTask context :: tasks).length))
      context.pendingStart context.pendingCount context.pendingNode
      (BitVec.ofNat 64 (rightTask context).start) (BitVec.ofNat 64 (rightTask context).input.length)
      (rightTask context).parent (BitVec.ofNat 64 (rightTask context).parentPosition) := by
  have index : BitVec.ofNat 64 (tasks.length + 1) - 1#64 = context.depth := by
    rw [depth, BitVec.ofNat_add]
    exact BitVec.add_sub_cancel _ _
  have zeroLe : zeroCount context ≤ context.input.length := List.length_filter_le _ _
  have startWord := SplitCount.post_word source context distinct
    (context.pendingStart + context.depth * 8#64, BitVec.ofNat 64 context.start + BitVec.ofNat 64 (zeroCount context))
    (by simp [SplitCount.writes, SplitProgram.allocationWrites])
  have countWord := SplitCount.post_word source context distinct
    (context.pendingCount + context.depth * 8#64, BitVec.ofNat 64 context.input.length - BitVec.ofNat 64 (zeroCount context))
    (by simp [SplitCount.writes, SplitProgram.allocationWrites])
  have parentWord := SplitCount.post_word source context distinct
    (context.pendingNode + context.depth * 8#64, context.node)
    (by simp [SplitCount.writes, SplitProgram.allocationWrites])
  have bitWord := SplitCount.post_word source context distinct (context.node, BitVec.ofNat 64 context.position)
    (by simp [SplitCount.writes, SplitProgram.allocationWrites])
  have sub : BitVec.ofNat 64 context.input.length - BitVec.ofNat 64 (zeroCount context) =
      BitVec.ofNat 64 (rightTask context).input.length := by
    rw [right_length, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) zeroLe]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try simp only [List.length_cons, index]
  · exact mapped.startMapped
  · simpa only [rightTask, ← BitVec.ofNat_add] using startWord
  · exact mapped.countMapped
  · simpa only [sub] using countWord
  · exact mapped.parentMapped
  · exact parentWord
  · exact mapped.nodeMapped
  · exact bitWord

/-- The actual seven stores prepend exactly the pending right task. Each old
suffix/parent word is protected by explicit interval/allocation separation. -/
theorem push_represents {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) (tasks : List Task)
    (depth : context.depth = BitVec.ofNat 64 tasks.length) (small : context.input.length < 2 ^ 64)
    (distinct : ((SplitCount.writes context).map Prod.fst).Nodup)
    (mapped : SplitProgram.Mapped source context.node context.depth context.dest
      context.pendingStart context.pendingCount context.pendingNode)
    (rep : Represents source context.pendingStart context.pendingCount context.pendingNode tasks)
    (srcAway : ∀ query, reads context.pendingStart context.pendingCount context.pendingNode tasks query →
      ∀ offset < context.input.length,
        query ≠ BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (dstAway : ∀ query, reads context.pendingStart context.pendingCount context.pendingNode tasks query →
      ∀ offset < context.input.length,
        query ≠ BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (allocationAway : ∀ query, reads context.pendingStart context.pendingCount context.pendingNode tasks query →
      query ∉ (SplitCount.writes context).map Prod.fst) :
    Represents (SplitCount.post source context) context.pendingStart context.pendingCount context.pendingNode
      (rightTask context :: tasks) := by
  refine ⟨push_head_cells source context tasks depth small distinct mapped, ?_⟩
  exact represents_of_agreement source (SplitCount.post source context) rfl _ _ _ tasks
    (fun query member => (SplitCount.post_away source context query
      (srcAway query member) (dstAway query member) (allocationAway query member)).symm) rep

end InitECandidate.Solver.WitnessRadix.PendingStack

#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.push_head_cells
#print axioms InitECandidate.Solver.WitnessRadix.PendingStack.push_represents
