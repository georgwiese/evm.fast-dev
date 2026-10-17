import InitECandidate.Solver.WitnessRadix.BuildProgram
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.WitnessRadix.BuildCopy
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open QueryBranch BuildProgram

def row (base start index : BitVec 64) : BitVec 64 := base + (start + index) * 8#64

theorem address_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (name : String) (base start index : BitVec 64)
    (baseLocal : source.locals.lookup (ofString name) = some (.val (.word base)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    eval source (arrayAddress name) = some (.val (.word (row base start index))) := by
  classical
  simp [eval, arrayAddress, row, localVar, evalHOLExact, evalListHOLExact, toExact,
    baseLocal, startLocal, indexLocal, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]

theorem load_read {F : Type} (source : PanSemStateFiniteExact 64 F)
    (base start index value : BitVec 64)
    (baseLocal : source.locals.lookup (ofString "dst") = some (.val (.word base)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (mapped : source.memaddrs (row base start index))
    (stored : source.memory (row base start index) = .word value) :
    eval source (.load .one (arrayAddress "dst")) = some (.val (.word value)) := by
  classical
  have address := address_read source "dst" base start index baseLocal startLocal indexLocal
  simp only [eval] at address
  simp only [eval, evalHOLExact, address, isWfShapeExactHOL, memLoadHOLExact, toExact,
    mapped, stored, ↓reduceIte]

theorem increment_execute {F : Type} (source : PanSemStateFiniteExact 64 F) (index : BitVec 64)
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState source increment = (none, bind source "i" (index + 1#64)) := by
  classical
  rw [increment, evaluateHOLFiniteState_assign]
  have valid : isValidValueHOLFinite source .local (ofString "i") (.val (.word (index + 1#64))) = true := by
    simp [isValidValueHOLFinite, lookupKvarHOLFinite, indexLocal, shapeOfHOLExact, shapeEqHOL]
  simp [addConst, localVar, evalHOLExact, evalListHOLExact, toExact, indexLocal,
    valueIsWord, valueWord, wordOpHOL, wordOp, ← isValidValueHOLFinite_eq, valid,
    setKvarHOLFinite, QueryBranch.bind]

/-- One iteration of the literal copy loop. Both source and destination are
actual mapped cells, and the exact updated memory function is exposed. -/
theorem body_execute {F : Type} (source : PanSemStateFiniteExact 64 F)
    (src dst start index value : BitVec 64)
    (srcLocal : source.locals.lookup (ofString "src") = some (.val (.word src)))
    (dstLocal : source.locals.lookup (ofString "dst") = some (.val (.word dst)))
    (startLocal : source.locals.lookup (ofString "start") = some (.val (.word start)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (destinationMapped : source.memaddrs (row src start index))
    (sourceMapped : source.memaddrs (row dst start index))
    (stored : source.memory (row dst start index) = .word value) :
    evaluateHOLFiniteState source copyBody =
      (none, bind { source with memory := StoreWord.put source.memory (row src start index) value }
        "i" (index + 1#64)) := by
  classical
  have write := StoreWord.execute source (arrayAddress "src") (.load .one (arrayAddress "dst"))
    (row src start index) value
    (address_read source "src" src start index srcLocal startLocal indexLocal)
    (load_read source dst start index value dstLocal startLocal indexLocal sourceMapped stored)
    destinationMapped
  let updated := { source with memory := StoreWord.put source.memory (row src start index) value }
  have incremented := increment_execute updated index indexLocal
  rw [copy_body_shape, evaluateHOLFiniteState_seq, write]
  simpa [fixClockHOLFinite, updated] using incremented

end InitECandidate.Solver.WitnessRadix.BuildCopy

#print axioms InitECandidate.Solver.WitnessRadix.BuildCopy.body_execute
