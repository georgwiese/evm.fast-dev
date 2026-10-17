import InitECandidate.Solver.WitnessRadix.LayoutOtherInterval
import InitECandidate.Solver.WitnessRadix.LayoutChildOwnership
import InitECandidate.Solver.WitnessRadix.PendingIntervals

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

def PendingRows {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout) (tasks : List PendingStack.Task) : Prop :=
  ∀ task ∈ tasks, BuildCopy.Rows source.memory source.memaddrs layout.primary (BitVec.ofNat 64 task.start) 0 task.input

theorem split_pending_rows {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (currentRows : BuildCopy.Rows source.memory source.memaddrs context.src (BitVec.ofNat 64 context.start) 0 context.input)
    (tasks : List PendingStack.Task) (fits : ∀ task ∈ tasks, task.start + task.input.length ≤ layout.count)
    (ordered : PendingStack.OrderedFrom (context.start + context.input.length) tasks)
    (rows : PendingRows source layout tasks) :
    PendingRows (SplitCount.post source context) layout (PendingStack.rightTask context :: tasks) := by
  have allocation : context.src.toNat + 8 * context.limit < 2 ^ 64 := by
    rw [atLayout.srcEq, atLayout.limitEq]
    have bound : layout.primary.toNat + 8 * layout.capacity < 2 ^ 64 := valid.noWrap .primary
    have room := valid.room
    omega
  have currentFits : context.start + context.input.length ≤ context.limit := by rw [atLayout.limitEq]; exact atLayout.interval
  have children := SplitCount.child_rows source context currentFits allocation currentRows
    (active_rows_away layout context allocated depth destination atLayout valid branchRoom stackRoom)
  intro task member
  rcases List.mem_cons.mp member with head | tail
  · subst task
    have right := children.2
    rw [atLayout.srcEq] at right
    exact right
  · exact other_interval_rows source layout context allocated depth destination atLayout valid branchRoom stackRoom
      task.start task.input (fits task tail)
      (Or.inr (PendingStack.ordered_start _ tasks ordered task tail)) (rows task tail)

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_pending_rows
