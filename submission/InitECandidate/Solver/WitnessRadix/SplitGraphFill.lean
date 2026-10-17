import InitECandidate.Solver.WitnessRadix.SplitGraph

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack PanSemStateFiniteExact
open SplitScope

def branchReplacement (context : SplitContext) (zero one : Graph.Tree) : OpenGraph.Tree :=
  .branch context.dest context.node context.position
    (.hole (context.node + 8#64) zero) (.hole (context.node + 16#64) one)

/-- Complete actual split execution installs the selected branch in the open
memory graph. Spatial ownership remains an explicit parent invariant. -/
theorem execute_fill {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) (table keys vals : BitVec 64) (zero one : Graph.Tree)
    (before after : OpenGraph.Tree)
    (step : OpenGraph.ReplaceHole context.dest (.branch context.position zero one)
      (branchReplacement context zero one) before after)
    (oldRep : OpenGraph.Represents source table keys vals before)
    (distinct : ((writes context).map Prod.fst).Nodup)
    (nonzero : context.node ≠ 0#64) (even : context.node &&& 1#64 = 0#64)
    (srcAway : ∀ query, OpenGraph.reads source table keys vals before query →
      ∀ offset < context.input.length,
        query ≠ BuildCopy.row context.src (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (dstAway : ∀ query, OpenGraph.reads source table keys vals before query →
      ∀ offset < context.input.length,
        query ≠ BuildCopy.row context.dst (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 offset))
    (allocationAway : ∀ query, OpenGraph.reads source table keys vals before query →
      query ∉ (writes context).map Prod.fst) :
    evaluateHOLFiniteState source TerminalProgram.remainingCode = (none, post source context) ∧
      OpenGraph.Represents (post source context) table keys vals after ∧
      OpenGraph.expected after = OpenGraph.expected before := by
  refine ⟨execute source context premises, ?_, OpenGraph.replacement_expected step rfl⟩
  apply OpenGraph.replacement_represents source (post source context) rfl rfl table keys vals step rfl
  · exact new_branch source context table keys vals zero one distinct premises.mapped nonzero even premises.inside
  · intro query member
    exact (post_away source context query (srcAway query member) (dstAway query member) (allocationAway query member)).symm
  · exact oldRep

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.execute_fill
