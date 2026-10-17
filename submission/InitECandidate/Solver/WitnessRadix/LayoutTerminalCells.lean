import InitECandidate.Solver.WitnessRadix.LayoutStackFrame
import InitECandidate.Solver.WitnessRadix.RowsLast

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open SplitScope

theorem terminal_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (locals : SplitCount.TaskLocals source context) :
    PopProgram.Locals source context.depth (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
      (BitVec.ofNat 64 context.position) context.dest context.pendingStart context.pendingCount context.pendingNode :=
  ⟨locals.depthLocal, locals.startLocal, locals.countLocal, locals.bitLocal, locals.destLocal,
    locals.pendingStartLocal, locals.pendingCountLocal, locals.pendingNodeLocal⟩

theorem terminal_head_cells {F : Type} (source : PanSemStateFiniteExact 64 F) (layout : Layout)
    (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (task : PendingStack.Task) (rest : List PendingStack.Task)
    (length : (task :: rest).length = depth)
    (rep : PendingStack.Represents source context.pendingStart context.pendingCount context.pendingNode (task :: rest)) :
    PopProgram.Cells source context.depth context.pendingStart context.pendingCount context.pendingNode
      (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length) task.parent (BitVec.ofNat 64 task.parentPosition) := by
  rw [atLayout.depthEq, ← length]
  exact PendingStack.head_cells source _ _ _ task rest rep

theorem terminal_store_safe (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (valid : Valid layout)
    (branchRoom : allocated < layout.count) (stackRoom : depth < layout.count)
    (task : PendingStack.Task) (rest : List PendingStack.Task) (length : (task :: rest).length = depth)
    (parents : ParentsWithin layout allocated (task :: rest)) :
    PopProgram.StoreSafe context.dest context.depth context.pendingStart context.pendingCount context.pendingNode task.parent := by
  have depthWord : context.depth = BitVec.ofNat 64 (rest.length + 1) := by rw [atLayout.depthEq, ← length]; rfl
  have apart (query : BitVec 64)
      (read : PendingStack.reads context.pendingStart context.pendingCount context.pendingNode (task :: rest) query) :
      query ≠ context.dest := by
    rw [atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq] at read
    have zone := pending_read_zone layout allocated (task :: rest) parents query read
    rw [length] at zone
    have absent := stack_allocation_separate layout context allocated depth destination atLayout valid branchRoom stackRoom query zone
    intro same
    subst query
    apply absent
    simp [SplitCount.writes, SplitProgram.allocationWrites]
  refine ⟨apart _ ?_, apart _ ?_, apart _ ?_, apart _ ?_⟩
  · rw [depthWord]; exact Or.inl rfl
  · rw [depthWord]; exact Or.inr (Or.inl rfl)
  · rw [depthWord]; exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_head_cells
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.terminal_store_safe
