import InitECandidate.Solver.Headers.StoreSyntax
import InitECandidate.Solver.Headers.FieldState
import InitECandidate.Solver.Headers.StoreNormalFrame

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- One actual original output-header scalar/tuple store retains the full
current field state. Word count comes from the reached helper slot type;
physical separation comes from the original header allocation. -/
theorem FieldState.store_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (offset : Nat) (value : StoreValue) (ready : value.Ready active) (within : offset+8*value.words≤248)
    (normal : evaluateHOLFiniteState source (storeProgram offset value)=(none,target)) :
    FieldState target pointer array header cursor limit current bytes cutoff items active := by
  obtain ⟨actual,valueRead,size⟩ := value.read source active state.slots current state.currentCell ready
  have addressRead : eval source (storeAddress offset)=some (.val (.word (header+BitVec.ofNat 64 offset))) := by
    simp [storeAddress,eval,evalHOLExact,evalListHOLExact,toExact,state.headerCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have number : (header+BitVec.ofNat 64 offset).toNat=header.toNat+offset :=
    MemoryBytes.offset_toNat header offset (by have h:=state.headerArena.upper; omega)
  obtain ⟨nextSlices,locals,globals⟩ := state.slices.normal_store_after source target pointer array cursor limit (header+BitVec.ofNat 64 offset)
    bytes cutoff value.words items (storeAddress offset) value.expression actual addressRead valueRead (by rw [size])
    (by rw [number]; have h:=state.recordsBeforeHeader; omega) (by rw [number]; have h:=state.headerArena.upper; omega) normal
  have fields:=Input.evaluation_fields source target (storeProgram offset value) none normal
  apply state.of_parts source target pointer array header cursor limit current bytes cutoff items active active nextSlices
    (state.slots.of_locals source target active locals) fields.2.2.2 (fun key=>by rw [globals])
  · rw [locals]
    exact state.arrayCell
  · rw [locals]
    exact state.headerCell
  · rw [locals]
    exact state.currentCell

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.FieldState.store_normal
