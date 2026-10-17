import InitECandidate.Solver.WitnessRadix.SplitScopeState
import InitECandidate.Solver.WitnessRadix.ScopedFrame

namespace InitECandidate.Solver.WitnessRadix.SplitScope
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem restored_cursors {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    restore source "zero_cursor" (restore (cursorState source context) "one_cursor" (sorted source context)) =
      base source context := by
  have savedOne : (cursorState source context).locals.lookup (ofString "one_cursor") =
      source.locals.lookup (ofString "one_cursor") :=
    bind_lookup_other source "zero_cursor" "one_cursor" _ (by decide)
  rw [restore_saved (cursorState source context) source (sorted source context) "one_cursor" savedOne]
  exact restore_two_frame source (sorted source context) (base source context) "zero_cursor" "one_cursor"
    (by decide) (sorted_other source context premises) rfl (sorted_frame source context premises)

/-- The actual two cursor declarations, stable scatter/copy and branch push,
including restoration of both cursor bindings. -/
theorem execute {F : Type} (source : PanSemStateFiniteExact 64 F) (context : SplitContext)
    (premises : Inputs source context) :
    evaluateHOLFiniteState source UnaryProgram.splitCode = (none, post source context) := by
  classical
  have startRead : eval source (localVar "start") =
      some (.val (.word (BitVec.ofNat 64 context.start))) := by
    simp [eval, localVar, evalHOLExact, toExact, premises.locals.startLocal]
  have startCursor : (cursorState source context).locals.lookup (ofString "start") =
      source.locals.lookup (ofString "start") :=
    bind_lookup_other source "zero_cursor" "start" _ (by decide)
  have zerosCursor : (cursorState source context).locals.lookup (ofString "zeros") =
      source.locals.lookup (ofString "zeros") :=
    bind_lookup_other source "zero_cursor" "zeros" _ (by decide)
  have oneRead : eval (cursorState source context) (.op .add [localVar "start", localVar "zeros"]) =
      some (.val (.word (BitVec.ofNat 64 (context.start + zeroCount context)))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, toExact, startCursor, zerosCursor,
      premises.locals.startLocal, premises.locals.zerosLocal, valueIsWord, valueWord, wordOpHOL, wordOp,
      BitVec.ofNat_add]
  have allocationRun := SplitProgram.allocation_execute (sorted source context) context.node context.depth
    (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
    (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
    context.dest context.pendingStart context.pendingCount context.pendingNode
    (allocation_locals source context premises) (allocation_mapped source context premises)
  have middleRun := (SortProgram.execute (entered source context) context.src context.dst context.keys
    context.keyFor context.input context.position context.start context.limit
    (sort_inputs source context premises) SplitProgram.allocationCode).trans allocationRun
  simp only [eval] at startRead oneRead
  rw [SplitProgram.split_shape, evaluateHOLFiniteState_dec_total]
  simp only [startRead, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState (cursorState source context)
      (.dec (ofString "one_cursor") .one (.op .add [localVar "start", localVar "zeros"])
        (SortProgram.code SplitProgram.allocationCode)));
    (output.1, restore source "zero_cursor" output.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  simp only [oneRead, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState (entered source context) (SortProgram.code SplitProgram.allocationCode);
    (output.1, restore source "zero_cursor" (restore (cursorState source context) "one_cursor" output.2))) = _
  rw [middleRun]
  change (none, restore source "zero_cursor" (restore (cursorState source context) "one_cursor"
    (SplitProgram.branchPost (sorted source context) context.node context.depth
      (BitVec.ofNat 64 context.start) (BitVec.ofNat 64 context.input.length)
      (BitVec.ofNat 64 (zeroCount context)) (BitVec.ofNat 64 context.position)
      context.dest context.pendingStart context.pendingCount context.pendingNode))) = _
  rw [SplitProgram.restore_branch _ _ "one_cursor" _ _ _ _ _ _ _ _ _ _
        (by decide) (by decide) (by decide) (by decide) (by decide),
      SplitProgram.restore_branch _ _ "zero_cursor" _ _ _ _ _ _ _ _ _ _
        (by decide) (by decide) (by decide) (by decide) (by decide), restored_cursors source context premises]
  rfl

end InitECandidate.Solver.WitnessRadix.SplitScope

#print axioms InitECandidate.Solver.WitnessRadix.SplitScope.execute
