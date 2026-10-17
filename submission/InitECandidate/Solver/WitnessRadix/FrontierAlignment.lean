import InitECandidate.Solver.WitnessRadix.ResumeContext
import InitECandidate.Solver.WitnessRadix.LayoutLeafGraph
import InitECandidate.Solver.WitnessRadix.OrdinalTree
import InitECandidate.Solver.WitnessRadix.LayoutLeftContext
import InitECandidate.Solver.WitnessRadix.OpenGraphFrontier

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open SplitScope

def currentTree (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) : Graph.Tree :=
  OrdinalTree.tree context.keyFor sliceFor context.position context.input

def savedHole (keyFor : BitVec 64 → ByteKeys.Key) (sliceFor : BitVec 64 → Graph.Slice) (task : PendingStack.Task) :
    BitVec 64 × Graph.Tree :=
  (task.parent + 16#64, OrdinalTree.tree keyFor sliceFor (task.parentPosition + 1) task.input)

def Aligned (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (tasks : List PendingStack.Task) (tree : OpenGraph.Tree) : Prop :=
  OpenGraph.frontier tree = (context.dest, currentTree context sliceFor) :: tasks.map (savedHole context.keyFor sliceFor)

def splitReplacement (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) : OpenGraph.Tree :=
  SplitCount.branchReplacement context
    (OrdinalTree.tree context.keyFor sliceFor (context.position + 1)
      (context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal))
    (OrdinalTree.tree context.keyFor sliceFor (context.position + 1)
      (context.input.filter (ScatterProgram.keep context.keyFor context.position)))

theorem split_aligned (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (tasks : List PendingStack.Task)
    (before after : OpenGraph.Tree)
    (aligned : Aligned context sliceFor tasks before)
    (step : OpenGraph.FillFirst context.dest (currentTree context sliceFor) (splitReplacement context sliceFor) before after) :
    Aligned (SplitCount.leftContext context) sliceFor (PendingStack.rightTask context :: tasks) after := by
  obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
  have same : pending = tasks.map (savedHole context.keyFor sliceFor) :=
    (List.cons.inj (oldFrontier.symm.trans aligned)).2
  rw [same] at nextFrontier
  change OpenGraph.frontier after = _
  rw [nextFrontier]
  rfl

theorem leaf_remaining (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (tasks : List PendingStack.Task)
    (before after : OpenGraph.Tree) (ordinal : Nat)
    (aligned : Aligned context sliceFor tasks before)
    (step : OpenGraph.FillFirst context.dest (currentTree context sliceFor) (completedLeaf context sliceFor ordinal) before after) :
    OpenGraph.frontier after = tasks.map (savedHole context.keyFor sliceFor) := by
  obtain ⟨pending, oldFrontier, nextFrontier⟩ := OpenGraph.fill_frontier step
  have same : pending = tasks.map (savedHole context.keyFor sliceFor) :=
    (List.cons.inj (oldFrontier.symm.trans aligned)).2
  simpa only [completedLeaf, OpenGraph.frontier, List.nil_append, same] using nextFrontier

theorem pop_aligned (context : SplitContext) (sliceFor : BitVec 64 → Graph.Slice) (task : PendingStack.Task)
    (rest : List PendingStack.Task) (tree : OpenGraph.Tree)
    (frontier : OpenGraph.frontier tree = (task :: rest).map (savedHole context.keyFor sliceFor)) :
    Aligned (resumeContext context task rest.length) sliceFor rest tree := frontier

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.split_aligned
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.leaf_remaining
#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.pop_aligned
