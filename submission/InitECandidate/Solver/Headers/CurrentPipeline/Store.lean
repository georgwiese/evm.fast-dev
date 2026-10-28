import InitECandidate.Solver.Headers.CurrentPipeline.State
import InitECandidate.Solver.Headers.CurrentHelpers.Store

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual typed scalar/tuple write lies in the allocated output header,
retaining all current physical input, record and active-local facts. -/
theorem State.store_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : State source pointer array header current bytes items active)
    (offset : Nat) (value : StoreValue) (ready : value.Ready active) (within : offset+8*value.words≤248)
    (normal : evaluateHOLFiniteState source (storeProgram offset value)=(none,target)) :
    State target pointer array header current bytes items active := by
  obtain ⟨actual,valueRead,size⟩:=value.read source active state.slots current state.currentCell ready
  have addressRead : eval source (storeAddress offset)=some (.val (.word (header+BitVec.ofNat 64 offset))) := by
    simp [storeAddress,eval,evalHOLExact,evalListHOLExact,toExact,state.headerCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset :=
    MemoryBytes.offset_toNat header offset (by have h:=state.headerArena.upper; omega)
  obtain ⟨nextSlices,locals,globals⟩:=state.slices.normal_store_after source target pointer array (header+BitVec.ofNat 64 offset)
    bytes value.words items (storeAddress offset) value.expression actual addressRead valueRead (by rw [size])
    (by rw [number]; have h:=state.recordsBeforeHeader; omega) (by rw [number]; have h:=state.headerArena.upper; omega) normal
  apply state.of_parts active nextSlices (state.slots.of_locals source target active locals) globals
  · rw [locals]; exact state.arrayCell
  · rw [locals]; exact state.headerCell
  · rw [locals]; exact state.currentCell

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.store_normal
