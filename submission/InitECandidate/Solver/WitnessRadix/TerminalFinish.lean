import InitECandidate.Solver.WitnessRadix.TerminalProgram
import InitECandidate.Solver.WitnessRadix.BuildEmpty
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.WitnessRadix.TerminalProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem finish_depth_zero {F : Type} (source : PanSemStateFiniteExact 64 F)
    (depth : source.locals.lookup (ofString "depth") = some (.val (.word 0#64))) :
    evaluateHOLFiniteState source afterStore =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  classical
  have chosen : evaluateHOLFiniteState source (.ite depthTest BuildEntry.returnZero .skip) =
      (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
    rw [evaluateHOLFiniteState_ite]
    simpa [depthTest, localVar, evalHOLExact, toExact, depth,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using BuildEntry.zero_return source
  rw [after_store_shape]
  exact StateSteps.stopped_sequence source (emptyLocalsHOLFinite source) _ _ _ chosen (Nat.le_refl _)

theorem tag_read {F : Type} (source : PanSemStateFiniteExact 64 F) (ordinal : BitVec 64)
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal))) :
    eval source tagExpression = some (.val (.word (ordinal * 2#64 + 1#64))) := by
  classical
  simp [eval, tagExpression, localVar, evalHOLExact, evalListHOLExact, toExact,
    ordinalLocal, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

/-- Terminal store and actual final return, when no pending subtree remains.
This is the finishing transition of every nonempty construction run. -/
theorem terminal_finish {F : Type} (source : PanSemStateFiniteExact 64 F)
    (destination ordinal : BitVec 64)
    (readOrdinal : eval source ordinalExpression = some (.val (.word ordinal)))
    (destLocal : source.locals.lookup (ofString "dest") = some (.val (.word destination)))
    (depth : source.locals.lookup (ofString "depth") = some (.val (.word 0#64)))
    (mapped : source.memaddrs destination) :
    ∃ target : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState source terminalCode = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite
        { source with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) } := by
  classical
  let ordState := bind source "ordinal" ordinal
  have notDest : ofString "ordinal" ≠ ofString "dest" := by decide
  have notDepth : ofString "ordinal" ≠ ofString "depth" := by decide
  have dest' : ordState.locals.lookup (ofString "dest") = some (.val (.word destination)) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notDest, destLocal]
  have depth' : ordState.locals.lookup (ofString "depth") = some (.val (.word 0#64)) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notDepth, depth]
  have ordinal' : ordState.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)) := by
    simp [ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have destRead : eval ordState (localVar "dest") = some (.val (.word destination)) := by
    simp [eval, localVar, evalHOLExact, toExact, dest']
  have write := StoreWord.execute ordState (localVar "dest") tagExpression destination (ordinal * 2#64 + 1#64)
    destRead (tag_read ordState ordinal ordinal') mapped
  let written := { ordState with memory := StoreWord.put source.memory destination (ordinal * 2#64 + 1#64) }
  have afterRun := finish_depth_zero written depth'
  have sequence := (StateSteps.next_sequence ordState written
    (.store (localVar "dest") tagExpression) afterStore write (Nat.le_refl _)).trans afterRun
  simp only [eval] at readOrdinal
  have run : evaluateHOLFiniteState source terminalCode =
      (some (.returned (.val (.word 0#64))), restore source "ordinal" (emptyLocalsHOLFinite written)) := by
    rw [terminal_shape, evaluateHOLFiniteState_dec_total]
    simp only [readOrdinal, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
    change (let output := evaluateHOLFiniteState ordState (.seq (.store (localVar "dest") tagExpression) afterStore);
      (output.1, restore source "ordinal" output.2)) = _
    rw [sequence]
  exact ⟨_, run, rfl⟩

end InitECandidate.Solver.WitnessRadix.TerminalProgram

#print axioms InitECandidate.Solver.WitnessRadix.TerminalProgram.terminal_finish
