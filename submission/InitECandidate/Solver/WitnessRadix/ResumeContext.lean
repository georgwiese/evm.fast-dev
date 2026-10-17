import InitECandidate.Solver.WitnessRadix.PendingValidity
import InitECandidate.Solver.WitnessRadix.LayoutTerminalBody

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open SplitScope

def resumeContext (context : SplitContext) (task : PendingStack.Task) (remaining : Nat) : SplitContext :=
  { context with
    input := task.input
    start := task.start
    position := task.parentPosition + 1
    depth := BitVec.ofNat 64 remaining
    dest := task.parent + 16#64 }

def resumeDestination (layout : Layout) (parent : Nat) : Address := (.keys, 32 * layout.count + 24 * parent + 16)

theorem resume_layout (layout : Layout) (context : SplitContext) (allocated depth : Nat) (destination : Address)
    (atLayout : ContextAt layout context allocated depth destination) (task : PendingStack.Task) (remaining parent : Nat)
    (valid : ValidTask layout task) (parentBound : parent < allocated)
    (parentEq : task.parent = branchAddress layout.keys layout.count parent) :
    ContextAt layout (resumeContext context task remaining) allocated remaining (resumeDestination layout parent) := by
  refine ⟨atLayout.srcEq, atLayout.dstEq, atLayout.keysEq, atLayout.nodeEq, rfl, ?_, ?_,
    atLayout.pendingStartEq, atLayout.pendingCountEq, atLayout.pendingNodeEq, atLayout.limitEq, valid.interval, valid.ordinals⟩
  · change task.parent + 16#64 = cell layout .keys (32 * layout.count + 24 * parent + 16)
    rw [parentEq]
    exact branch_address_field layout.keys layout.count parent 2
  · exact ⟨parent, parentBound, 2, Or.inr rfl, rfl⟩

/-- Actual pop assignments recover all twelve live locals of the saved task. -/
theorem resume_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (task : PendingStack.Task) (remaining : Nat) (depthEq : context.depth = BitVec.ofNat 64 (remaining + 1))
    (locals : SplitCount.TaskLocals source context) :
    SplitCount.TaskLocals
      (PopProgram.popPost source context.depth (BitVec.ofNat 64 task.start) (BitVec.ofNat 64 task.input.length)
        task.parent (BitVec.ofNat 64 task.parentPosition)) (resumeContext context task remaining) := by
  rcases locals with ⟨src, dst, keys, next, depth, start, count, bit, dest, pendingStart, pendingCount, pendingNode⟩
  simp [ofString] at src dst keys next pendingStart pendingCount pendingNode
  constructor
  all_goals simp [resumeContext, PopProgram.popPost, QueryBranch.bind, setVarHOLFinite,
    HolFiniteMapExact.update, FUPDATE, ofString, src, dst, keys, next, pendingStart, pendingCount, pendingNode,
    depthEq, BitVec.ofNat_add, BitVec.add_sub_cancel]

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.resume_layout
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.resume_locals
