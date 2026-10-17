import InitECandidate.Solver.WitnessRadix.ScatterBucket

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

def post {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64) : PanSemStateFiniteExact 64 F :=
  let written := ({ source with
    memory := StoreWord.put source.memory
      (dst + (if digit = 0#64 then zeroCursor else oneCursor) * 8#64) ordinal });
  bind (if digit = 0#64 then bind written "zero_cursor" (zeroCursor + 1#64)
    else bind written "one_cursor" (oneCursor + 1#64)) "i" (index + 1#64)

theorem after_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (digitLocal : source.locals.lookup (ofString "digit") = some (.val (.word digit)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word zeroCursor)))
    (oneLocal : source.locals.lookup (ofString "one_cursor") = some (.val (.word oneCursor)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (dst + (if digit = 0#64 then zeroCursor else oneCursor) * 8#64)) :
    evaluateHOLFiniteState source afterDigit = (none, post source dst digit ordinal zeroCursor oneCursor index) := by
  classical
  by_cases zero : digit = 0#64
  · have chosen : evaluateHOLFiniteState source
        (.ite CountProgram.digitTest (writeBucket "zero_cursor") (writeBucket "one_cursor")) =
        evaluateHOLFiniteState source (writeBucket "zero_cursor") := by
      rw [evaluateHOLFiniteState_ite]
      simp [CountProgram.digitTest, localVar, evalHOLExact, toExact, digitLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have sequence : evaluateHOLFiniteState source afterDigit =
        evaluateHOLFiniteState source (.seq (writeBucket "zero_cursor") BuildProgram.increment) := by
      rw [afterDigit, evaluateHOLFiniteState_seq, evaluateHOLFiniteState_seq, chosen]
    rw [sequence]
    have result := bucket_increment source "zero_cursor" dst zeroCursor ordinal index (by decide)
      dstLocal zeroLocal ordinalLocal indexLocal (by simpa only [if_pos zero] using mapped)
    simpa only [post, if_pos zero] using result
  · have chosen : evaluateHOLFiniteState source
        (.ite CountProgram.digitTest (writeBucket "zero_cursor") (writeBucket "one_cursor")) =
        evaluateHOLFiniteState source (writeBucket "one_cursor") := by
      rw [evaluateHOLFiniteState_ite]
      simp [CountProgram.digitTest, localVar, evalHOLExact, toExact, digitLocal, zero,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    have sequence : evaluateHOLFiniteState source afterDigit =
        evaluateHOLFiniteState source (.seq (writeBucket "one_cursor") BuildProgram.increment) := by
      rw [afterDigit, evaluateHOLFiniteState_seq, evaluateHOLFiniteState_seq, chosen]
    rw [sequence]
    have result := bucket_increment source "one_cursor" dst oneCursor ordinal index (by decide)
      dstLocal oneLocal ordinalLocal indexLocal (by simpa only [if_neg zero] using mapped)
    simpa only [post, if_neg zero] using result

theorem restore_post {F : Type} (saved state : PanSemStateFiniteExact 64 F) (name : String)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64)
    (notI : ofString name ≠ ofString "i")
    (notZero : ofString name ≠ ofString "zero_cursor") (notOne : ofString name ≠ ofString "one_cursor") :
    restore saved name (post state dst digit ordinal zeroCursor oneCursor index) =
      post (restore saved name state) dst digit ordinal zeroCursor oneCursor index := by
  by_cases zero : digit = 0#64
  · simp only [post, if_pos zero]
    rw [restore_bind_other saved _ name "i" _ notI,
      restore_bind_other saved _ name "zero_cursor" _ notZero]
    rfl
  · simp only [post, if_neg zero]
    rw [restore_bind_other saved _ name "i" _ notI,
      restore_bind_other saved _ name "one_cursor" _ notOne]
    rfl

/-- Actual scatter body including both scoped declarations and restoration.
The single concrete destination store is the only memory change. -/
theorem body_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (dst digit ordinal zeroCursor oneCursor index : BitVec 64)
    (readOrdinal : eval source CountProgram.ordinalExpression = some (.val (.word ordinal)))
    (readDigit : eval (bind source "ordinal" ordinal) CountProgram.digitExpression = some (.val (.word digit)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (zeroLocal : source.locals.lookup (ofString "zero_cursor") = some (.val (.word zeroCursor)))
    (oneLocal : source.locals.lookup (ofString "one_cursor") = some (.val (.word oneCursor)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (dst + (if digit = 0#64 then zeroCursor else oneCursor) * 8#64)) :
    evaluateHOLFiniteState source body = (none, post source dst digit ordinal zeroCursor oneCursor index) := by
  classical
  let ordState := bind source "ordinal" ordinal
  let digState := bind ordState "digit" digit
  have lookupOther (name : String) (notOrd : ofString "ordinal" ≠ ofString name)
      (notDigit : ofString "digit" ≠ ofString name) :
      digState.locals.lookup (ofString name) = source.locals.lookup (ofString name) := by
    simp [digState, ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update,
      FUPDATE, notOrd, notDigit]
  have digitLocal : digState.locals.lookup (ofString "digit") = some (.val (.word digit)) := by
    simp [digState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have ordinalDigit : ofString "digit" ≠ ofString "ordinal" := by decide
  have ordinalLocal : digState.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)) := by
    simp [digState, ordState, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, ordinalDigit]
  have result := after_execute digState dst digit ordinal zeroCursor oneCursor index
    ((lookupOther "dst" (by decide) (by decide)).trans dstLocal) digitLocal ordinalLocal
    ((lookupOther "zero_cursor" (by decide) (by decide)).trans zeroLocal)
    ((lookupOther "one_cursor" (by decide) (by decide)).trans oneLocal)
    ((lookupOther "i" (by decide) (by decide)).trans indexLocal) mapped
  change eval ordState CountProgram.digitExpression = _ at readDigit
  simp only [eval] at readOrdinal readDigit
  rw [body_shape, evaluateHOLFiniteState_dec_total]
  simp only [readOrdinal, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := (evaluateHOLFiniteState ordState
      (.dec (ofString "digit") .one CountProgram.digitExpression afterDigit));
    (output.1, restore source "ordinal" output.2)) = _
  rw [evaluateHOLFiniteState_dec_total]
  simp only [readDigit, shapeOfHOLExact, shapeEqHOL, ↓reduceIte]
  change (let output := evaluateHOLFiniteState digState afterDigit;
    (output.1, restore source "ordinal" (restore ordState "digit" output.2))) = _
  rw [result]
  change (none, restore source "ordinal" (restore ordState "digit"
    (post digState dst digit ordinal zeroCursor oneCursor index))) = _
  rw [restore_post ordState digState "digit" dst digit ordinal zeroCursor oneCursor index
    (by decide) (by decide) (by decide)]
  have digitRestored : restore ordState "digit" digState = ordState := restore_bound _ _ _
  rw [digitRestored, restore_post source ordState "ordinal" dst digit ordinal zeroCursor oneCursor index
    (by decide) (by decide) (by decide)]
  have ordinalRestored : restore source "ordinal" ordState = source := restore_bound _ _ _
  rw [ordinalRestored]

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.body_execute
