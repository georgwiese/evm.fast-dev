import InitECandidate.Solver.WitnessRadix.SplitScopeExecution

namespace InitECandidate.Solver.WitnessRadix.SplitScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem restore_post {F : Type} (saved source : PanSemStateFiniteExact 64 F) (context : SplitContext) (name : String)
    (notNext : ofString name ≠ ofString "node_next") (notDepth : ofString name ≠ ofString "depth")
    (notCount : ofString name ≠ ofString "count") (notDest : ofString name ≠ ofString "dest")
    (notBit : ofString name ≠ ofString "bit") :
    restore saved name (post source context) = post (restore saved name source) context := by
  unfold post
  rw [SplitProgram.restore_branch _ _ name _ _ _ _ _ _ _ _ _ _ notNext notDepth notCount notDest notBit]
  cases savedAt : saved.locals.lookup (ofString name) <;> rfl

theorem post_frame {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext) :
    emptyLocalsHOLFinite (post source context) = emptyLocalsHOLFinite { source with
      memory := SplitProgram.branchMemory
        (SortProgram.sortedMemory source.memory context.src context.dst context.keyFor context.position context.start context.input)
        context.node context.depth (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
        (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position) context.dest
        context.pendingStart context.pendingCount context.pendingNode
      clock := source.clock - 2 * context.input.length } := rfl

end InitECandidate.Solver.WitnessRadix.SplitScope

#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.restore_post
#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.post_frame
