import InitECandidate.Solver.WitnessRadix.CountDigit
import InitECandidate.Solver.WitnessRadix.BuildCopy

namespace InitECandidate.Solver.WitnessRadix.CountProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem increase_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (zeros : BitVec 64)
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros))) :
    evaluateHOLFiniteState source increaseZeros = (none, bind source "zeros" (zeros + 1#64)) := by
  classical
  rw [increaseZeros, evaluateHOLFiniteState_assign]
  have valid : isValidValueHOLFinite source .local (ofString "zeros") (.val (.word (zeros + 1#64))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, zerosLocal, shapeOfHOLExact, shapeEqHOL]
  simp [addConst, localVar, evalHOLExact, evalListHOLExact, toExact, zerosLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, ← isValidValueHOLFinite_eq, valid,
    setKvarHOLFinite, QueryBranch.bind]

def counterPost {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  bind (if digit = 0#64 then bind source "zeros" (zeros + 1#64) else source) "i" (index + 1#64)

theorem after_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (digit zeros index : BitVec 64)
    (digitLocal : source.locals.lookup (ofString "digit") = some (.val (.word digit)))
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState source afterDigit = (none, counterPost source digit zeros index) := by
  classical
  have zerosI : ofString "zeros" ≠ ofString "i" := by decide
  by_cases zero : digit = 0#64
  · have chosen : evaluateHOLFiniteState source (.ite digitTest increaseZeros .skip) =
        (none, bind source "zeros" (zeros + 1#64)) := by
      rw [evaluateHOLFiniteState_ite]
      simpa [digitTest, localVar, evalHOLExact, toExact, digitLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL] using increase_execute source zeros zerosLocal
    have index' : (bind source "zeros" (zeros + 1#64)).locals.lookup (ofString "i") =
        some (.val (.word index)) := by
      simp [QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, zerosI, indexLocal]
    have incremented := BuildCopy.increment_execute (bind source "zeros" (zeros + 1#64)) index index'
    rw [afterDigit, evaluateHOLFiniteState_seq, chosen]
    simpa [fixClockHOLFinite, QueryBranch.bind, setVarHOLFinite, counterPost, zero] using incremented
  · have chosen : evaluateHOLFiniteState source (.ite digitTest increaseZeros .skip) = (none, source) := by
      rw [evaluateHOLFiniteState_ite]
      simp [digitTest, localVar, evalHOLExact, toExact, digitLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have incremented := BuildCopy.increment_execute source index indexLocal
    rw [afterDigit, evaluateHOLFiniteState_seq, chosen]
    simpa [fixClockHOLFinite, counterPost, zero] using incremented

theorem restore_counters {F : Type} (saved state : PanSemStateFiniteExact 64 F)
    (name : String) (digit zeros index : BitVec 64)
    (notZeros : ofString name ≠ ofString "zeros") (notI : ofString name ≠ ofString "i") :
    restore saved name (counterPost state digit zeros index) =
      counterPost (restore saved name state) digit zeros index := by
  by_cases zero : digit = 0#64
  · simp only [counterPost, if_pos zero]
    rw [restore_bind_other saved _ name "i" _ notI,
      restore_bind_other saved state name "zeros" _ notZeros]
  · simp only [counterPost, if_neg zero]
    rw [restore_bind_other saved state name "i" _ notI]

/-- Exact counting-body execution from the actual ordinal and bit reads.
The declarations' ordinal/digit locals are restored; only i/zeros change. -/
theorem body_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (ordinal digit zeros index : BitVec 64)
    (readOrdinal : eval source ordinalExpression = some (.val (.word ordinal)))
    (readDigit : eval (bind source "ordinal" ordinal) digitExpression = some (.val (.word digit)))
    (zerosLocal : source.locals.lookup (ofString "zeros") = some (.val (.word zeros)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState source body = (none, counterPost source digit zeros index) := by
  classical
  let ordState := bind source "ordinal" ordinal
  let digState := bind ordState "digit" digit
  have names : ofString "ordinal" ≠ ofString "zeros" ∧ ofString "ordinal" ≠ ofString "i" ∧
      ofString "digit" ≠ ofString "zeros" ∧ ofString "digit" ≠ ofString "i" := by decide
  have zeros' : digState.locals.lookup (ofString "zeros") = some (.val (.word zeros)) := by
    simp [digState, ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, names.1, names.2.2.1, zerosLocal]
  have index' : digState.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [digState, ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, names.2.1, names.2.2.2, indexLocal]
  have digit' : digState.locals.lookup (ofString "digit") = some (.val (.word digit)) := by
    simp [digState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have afterResult := after_execute digState digit zeros index digit' zeros' index'
  change eval ordState digitExpression = _ at readDigit
  simp only [eval] at readOrdinal readDigit
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [readOrdinal, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := evaluateHOLFiniteState ordState (.dec (ofString "digit") .one digitExpression afterDigit);
    (result.1, restore source "ordinal" result.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  simp only [readDigit, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let result := evaluateHOLFiniteState digState afterDigit;
    (result.1, restore source "ordinal" (restore ordState "digit" result.2))) = _
  rw [afterResult]
  simp only [restore_counters _ _ "digit" digit zeros index names.2.2.1 names.2.2.2,
    restore_bound, restore_counters _ _ "ordinal" digit zeros index names.1 names.2.1]
  simp only [digState, ordState, restore_bound]

end InitECandidate.Solver.WitnessRadix.CountProgram

#print axioms InitECandidate.Solver.WitnessRadix.CountProgram.body_execute
