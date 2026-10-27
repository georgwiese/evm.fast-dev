import InitECandidate.Solver.Input.CopyState
import InitECandidate.Solver.Input.SharedReadReached
import InitECandidate.Solver.Input.WordStoreNormal
import InitECandidate.Solver.Input.NoneControl

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Invert the actual continuing input-copy instruction sequence. Readable
host bytes and the destination mapping are conclusions of that execution. -/
theorem copy_step_reached (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer index old : BitVec 64)
    (pointerLocal : source.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i") = some (.val (.word index)))
    (wordLocal : source.locals.lookup (ofString "w") = some (.val (.word old)))
    (oracleEq : source.ffi.oracle = InitE.sourceOracle)
    (normal : evaluateHOLFiniteState source copyBody = (none, target)) :
    source.memaddrs (pointer + index) ∧
    (∀ offset < 8, (source.ffi.ffiState
      (Guest.inputDataAddr + index + BitVec.ofNat 64 offset)).isSome = true) ∧
    target = wordPost source pointer index := by
  obtain ⟨loaded, readRun, tailRun⟩ := sequence_none source target _ _ normal
  obtain ⟨stored, storeRun, incrementRun⟩ := sequence_none loaded target _ _ tailRun
  have addressRead : eval source dataAddress = some (.val (.word (Guest.inputDataAddr + index))) := by
    simp [eval, dataAddress, localVar, evalHOLExact, evalListHOLExact, indexLocal,
      valueIsWord, valueWord, wordOpHOL, wordOp]
    rfl
  obtain ⟨mapped, next, answer, reply, cell⟩ := SharedRead.reached_reply source loaded "w"
    dataAddress _ old addressRead wordLocal readRun
  rw [oracleEq] at reply
  have present := SharedRead.oracle_return_present source.ffi.ffiState next _ answer reply
  have same := SharedRead.normal_post source loaded "w" dataAddress _ old
    addressRead wordLocal oracleEq readRun
  let value := Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState (Guest.inputDataAddr + index))
  have loadedP : loaded.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [same]
    exact (bind_lookup_other source "w" "p" value (by decide)).trans pointerLocal
  have loadedI : loaded.locals.lookup (ofString "i") = some (.val (.word index)) := by
    rw [same]
    exact (bind_lookup_other source "w" "i" value (by decide)).trans indexLocal
  have loadedW : loaded.locals.lookup (ofString "w") = some (.val (.word value)) := by
    rw [same]
    exact bind_lookup_same _ _ _
  have destinationRead : eval loaded (.op .add [localVar "p", localVar "i"]) =
      some (.val (.word (pointer + index))) := by
    simp [eval, localVar, evalHOLExact, evalListHOLExact, loadedP, loadedI,
      valueIsWord, valueWord, wordOpHOL, wordOp]
  have valueRead : eval loaded (localVar "w") = some (.val (.word value)) := by
    simpa [eval, localVar, evalHOLExact] using loadedW
  have storedFacts := word_store_normal loaded stored _ _ (pointer + index) value
    destinationRead valueRead storeRun
  have ordinaryMapped : source.memaddrs (pointer + index) := by
    rw [same] at storedFacts
    exact storedFacts.1
  have actual := copy_step source pointer index old pointerLocal indexLocal wordLocal
    oracleEq mapped ordinaryMapped present
  exact ⟨ordinaryMapped, present, congrArg Prod.snd (normal.symm.trans actual)⟩

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_step_reached
