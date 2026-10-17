import InitECandidate.Solver.WitnessRadix.SplitCountExecution

namespace InitECandidate.Solver.WitnessRadix.SplitCount
open Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open SplitScope QueryBranch

def leftContext (context : SplitContext) : SplitContext :=
  { context with
    node := context.node + 24#64
    depth := context.depth + 1#64
    dest := context.node + 8#64
    input := context.input.filter fun ordinal => !ScatterProgram.keep context.keyFor context.position ordinal
    position := context.position + 1 }

/-- The five persistent assignments select precisely the left child task;
all unchanged ABI/pending-array locals retain their original values. -/
theorem post_locals {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (locals : TaskLocals source context) : TaskLocals (post source context) (leftContext context) := by
  have other (name : String) (nn : ofString "node_next" ≠ ofString name) (nd : ofString "depth" ≠ ofString name)
      (nc : ofString "count" ≠ ofString name) (nt : ofString "dest" ≠ ofString name) (nb : ofString "bit" ≠ ofString name) :
      (post source context).locals.lookup (ofString name) = source.locals.lookup (ofString name) :=
    SplitProgram.branchPost_other _ _ _ _ _ _ _ _ _ _ _ _ nn nd nc nt nb
  refine ⟨(other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.srcLocal,
    (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.dstLocal,
    (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.keysLocal,
    ?_, ?_, (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.startLocal,
    ?_, ?_, ?_,
    (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.pendingStartLocal,
    (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.pendingCountLocal,
    (other _ (by decide) (by decide) (by decide) (by decide) (by decide)).trans locals.pendingNodeLocal⟩
  all_goals simp [post, SplitScope.post, SplitScope.base, SplitProgram.branchPost, leftContext, zeroCount,
    ScatterProgram.zeros, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ofString, BitVec.ofNat_add]

end InitECandidate.Solver.WitnessRadix.SplitCount

#print axioms InitECandidate.Solver.WitnessRadix.SplitCount.post_locals
