import InitECandidate.Solver.WitnessRadix.ScatterProgram
import InitECandidate.Solver.WitnessRadix.BuildCopy

namespace InitECandidate.Solver.WitnessRadix.ScatterProgram
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch

theorem cursor_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (dst cursor : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (cursorLocal : source.locals.lookup (ofString name) = some (.val (.word cursor))) :
    eval source (cursorAddress name) = some (.val (.word (dst + cursor * 8#64))) := by
  classical
  simp [eval, cursorAddress, localVar, evalHOLExact, evalListHOLExact, toExact,
    dstLocal, cursorLocal, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

theorem increase_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (cursor : BitVec 64)
    (cursorLocal : source.locals.lookup (ofString name) = some (.val (.word cursor))) :
    evaluateHOLFiniteState source (increaseCursor name) = (none, bind source name (cursor + 1#64)) := by
  classical
  rw [increaseCursor, evaluateHOLFiniteState_assign]
  have valid : isValidValueHOLFinite source .local (ofString name) (.val (.word (cursor + 1#64))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, cursorLocal, shapeOfHOLExact, shapeEqHOL]
  simp [addConst, localVar, evalHOLExact, evalListHOLExact, toExact, cursorLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, ← isValidValueHOLFinite_eq, valid,
    setKvarHOLFinite, QueryBranch.bind]

theorem bucket_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (dst cursor ordinal : BitVec 64)
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (cursorLocal : source.locals.lookup (ofString name) = some (.val (.word cursor)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (mapped : source.memaddrs (dst + cursor * 8#64)) :
    evaluateHOLFiniteState source (writeBucket name) =
      (none, bind { source with memory := StoreWord.put source.memory (dst + cursor * 8#64) ordinal }
        name (cursor + 1#64)) := by
  classical
  have ordinalRead : eval source (localVar "ordinal") = some (.val (.word ordinal)) := by
    simp [eval, localVar, evalHOLExact, toExact, ordinalLocal]
  have write := StoreWord.execute source (cursorAddress name) (localVar "ordinal")
    (dst + cursor * 8#64) ordinal (cursor_read source name dst cursor dstLocal cursorLocal) ordinalRead mapped
  let written := { source with memory := StoreWord.put source.memory (dst + cursor * 8#64) ordinal }
  have increased := increase_execute written name cursor cursorLocal
  rw [writeBucket, evaluateHOLFiniteState_seq, write]
  simpa [fixClockHOLFinite, written] using increased

theorem bucket_increment {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (dst cursor ordinal index : BitVec 64)
    (notI : ofString name ≠ ofString "i")
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (cursorLocal : source.locals.lookup (ofString name) = some (.val (.word cursor)))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word ordinal)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (dst + cursor * 8#64)) :
    evaluateHOLFiniteState source (.seq (writeBucket name) BuildProgram.increment) =
      (none, bind (bind { source with
        memory := StoreWord.put source.memory (dst + cursor * 8#64) ordinal }
        name (cursor + 1#64)) "i" (index + 1#64)) := by
  classical
  have bucket := bucket_execute source name dst cursor ordinal dstLocal cursorLocal ordinalLocal mapped
  let written := bind { source with memory := StoreWord.put source.memory (dst + cursor * 8#64) ordinal }
    name (cursor + 1#64)
  have index' : written.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [written, QueryBranch.bind, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, notI, indexLocal]
  have incremented := BuildCopy.increment_execute written index index'
  rw [evaluateHOLFiniteState_seq, bucket]
  simpa [fixClockHOLFinite, written, QueryBranch.bind, setVarHOLFinite] using incremented

end InitECandidate.Solver.WitnessRadix.ScatterProgram

#print axioms InitECandidate.Solver.WitnessRadix.ScatterProgram.bucket_execute
