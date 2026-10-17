import InitECandidate.Solver.Input.BlobProgram
import InitECandidate.Solver.Input.HostWords
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input.Blob
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

noncomputable def wordPost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index : BitVec 64) :
    PanSemStateFiniteExact 64 Guest.HostMemory :=
  let loaded:=SharedRead.post source "w" (Guest.inputDataAddr+index)
  WitnessRadix.QueryBranch.bind {loaded with memory:=(WitnessRadix.StoreWord.put loaded.memory (pointer+index)
    (Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState (Guest.inputDataAddr+index))))} "i" (index+8#64)

/-- One complete literal copy-loop body: actual host read, ordinary word store
and increment. No source clock is consumed inside the body. -/
theorem copy_step (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer index old : BitVec 64)
    (pointerLocal : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (indexLocal : source.locals.lookup (ofString "i")=some (.val (.word index)))
    (wordLocal : source.locals.lookup (ofString "w")=some (.val (.word old)))
    (oracleEq : source.ffi.oracle=InitE.sourceOracle)
    (sharedMapped : source.shMemaddrs (Guest.inputDataAddr+index))
    (ordinaryMapped : source.memaddrs (pointer+index))
    (present : ∀ offset<8,(source.ffi.ffiState (Guest.inputDataAddr+index+BitVec.ofNat 64 offset)).isSome=true) :
    evaluateHOLFiniteState source copyBody=(none,wordPost source pointer index) := by
  classical
  let loaded:=SharedRead.post source "w" (Guest.inputDataAddr+index)
  let value:=Guest.wordOfLeBytes (SharedRead.bytes source.ffi.ffiState (Guest.inputDataAddr+index))
  let stored : PanSemStateFiniteExact 64 Guest.HostMemory :=
    {loaded with memory:=WitnessRadix.StoreWord.put loaded.memory (pointer+index) value}
  have addressRead : eval source dataAddress=some (.val (.word (Guest.inputDataAddr+index))) := by
    simp [eval,dataAddress,localVar,evalHOLExact,evalListHOLExact,toExact,indexLocal,
      valueIsWord,valueWord,wordOpHOL,wordOp]
    rfl
  have readRun:=SharedRead.execute source "w" dataAddress (Guest.inputDataAddr+index) old
    addressRead wordLocal oracleEq sharedMapped present
  have loadedP : loaded.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
    exact (bind_lookup_other source "w" "p" value (by decide)).trans pointerLocal
  have loadedI : loaded.locals.lookup (ofString "i")=some (.val (.word index)) := by
    exact (bind_lookup_other source "w" "i" value (by decide)).trans indexLocal
  have loadedW : loaded.locals.lookup (ofString "w")=some (.val (.word value)) :=
    WitnessRadix.QueryBranch.bind_lookup_same _ _ _
  have destinationRead : eval loaded (.op .add [localVar "p",localVar "i"])=some (.val (.word (pointer+index))) := by
    simp [eval,localVar,evalHOLExact,evalListHOLExact,toExact,loadedP,loadedI,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval loaded (localVar "w")=some (.val (.word value)) := by
    simpa [eval,localVar,evalHOLExact,toExact] using loadedW
  have storeRun:=WitnessRadix.StoreWord.execute loaded _ _ (pointer+index) value destinationRead valueRead ordinaryMapped
  have nextRead : eval stored (addConst (localVar "i") 8#64)=some (.val (.word (index+8#64))) := by
    simp [eval,addConst,localVar,evalHOLExact,evalListHOLExact,toExact,stored,loadedI,valueIsWord,valueWord,wordOpHOL,wordOp]
  have incrementRun:=WitnessRadix.StateSteps.assign_execute stored "i" _ index (index+8#64) loadedI nextRead
  rw [copyBody,WitnessRadix.StateSteps.next_sequence source loaded _ _ readRun (Nat.le_refl _),
    WitnessRadix.StateSteps.next_sequence loaded stored _ _ storeRun (Nat.le_refl _),incrementRun]
  rfl

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.copy_step
