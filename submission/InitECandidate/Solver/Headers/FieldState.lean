import InitECandidate.Solver.Headers.StoreValue
import InitECandidate.Solver.Headers.HelperCall
import InitECandidate.Solver.Headers.SlotNames

namespace InitECandidate.Solver.Headers
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Current original field-pipeline data and active helper locals. Physical
input/record/header extents and the true21/23 branch bit are explicit; no
future output-header image or helper success is included. -/
structure FieldState (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active : List Slot) : Prop where
  slices : SliceState source pointer array cursor limit bytes cutoff items
  slots : Slots source active
  code : Input.OriginalCode.Installed source.code
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  headerCell : source.locals.lookup (ofString "h")=some (.val (.word header))
  currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word current))
  branch : (current=0#64 ∧ items.length=21) ∨ (current=1#64 ∧ items.length=23)
  inputArena : AllocatedBytes.Arena pointer bytes
  headerArena : AllocatedBytes.Arena header 248
  headerAligned : header.toNat%8=0
  recordsBeforeHeader : array.toNat+16*items.length≤header.toNat
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded header 248#64)))

theorem FieldState.of_parts (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff : Nat) (items : List Rlp.ListItem) (active nextActive : List Slot)
    (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (slices : SliceState target pointer array cursor limit bytes cutoff items) (slots : Slots target nextActive)
    (code : target.code=source.code) (globals : ∀ key,target.globals.lookup key=source.globals.lookup key)
    (arrayCell : target.locals.lookup (ofString "arr")=some (.val (.word array)))
    (headerCell : target.locals.lookup (ofString "h")=some (.val (.word header)))
    (currentCell : target.locals.lookup (ofString "is_current")=some (.val (.word current))) :
    FieldState target pointer array header cursor limit current bytes cutoff items nextActive :=
  ⟨slices,slots,by rw [code]; exact state.code,arrayCell,headerCell,currentCell,state.branch,state.inputArena,state.headerArena,
    state.headerAligned,state.recordsBeforeHeader,(globals _).trans state.heap⟩

/-- A checked actual helper return enters the original caller's next scope
with its real new slot, while retaining every current field-pipeline fact. -/
theorem FieldState.resume (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Helper.Kind)
    (pointer array header cursor limit current : BitVec 64) (bytes cutoff rowBytes : Nat) (items : List Rlp.ListItem) (active : List Slot)
    (state : FieldState source pointer array header cursor limit current bytes cutoff items active)
    (returned : Helper.Returned source target kind array pointer cursor limit bytes cutoff rowBytes items)
    (slot : Slot) (value : ValueHOL 64) (shape : shapeOfHOLExact value=slot.shape) :
    FieldState (Input.CallNormal.continuationEntry source target slot.text value)
      pointer array header cursor limit current bytes cutoff items (slot::active) := by
  let ready:=Input.CallNormal.continuationEntry source target slot.text value
  have slices : SliceState ready pointer array cursor limit bytes cutoff items :=
    returned.state.of_parts target ready pointer array cursor limit bytes cutoff items
      (Rlp.Validation.Arena.of_fields target ready cursor limit returned.state.arena rfl rfl) returned.state.records (by intro offset inside; rfl)
  have baseSlots : Slots {target with locals:=source.locals} active := state.slots.of_locals source _ active rfl
  have slots : Slots ready (slot::active) := by
    change Slots (setVarHOLFinite (ofString slot.text) value {target with locals:=source.locals}) (slot::active)
    rw [slot.of_text]
    exact baseSlots.set _ active slot value shape
  apply state.of_parts source ready pointer array header cursor limit current bytes cutoff items active (slot::active) slices slots returned.code returned.globals
  · simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_array,Ne.symm slot.not_array,state.arrayCell]
  · simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_header,Ne.symm slot.not_header,state.headerCell]
  · simp [ready,Input.CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_current,Ne.symm slot.not_current,state.currentCell]

end InitECandidate.Solver.Headers

#print axioms InitECandidate.Solver.Headers.Slot.of_text
#print axioms InitECandidate.Solver.Headers.Slot.not_array
#print axioms InitECandidate.Solver.Headers.Slot.not_header
#print axioms InitECandidate.Solver.Headers.Slot.not_current
#print axioms InitECandidate.Solver.Headers.FieldState.of_parts
#print axioms InitECandidate.Solver.Headers.FieldState.resume
