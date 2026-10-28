import InitECandidate.Solver.Headers.CurrentHelpers.Call
import InitECandidate.Solver.Headers.StoreSyntax
import InitECandidate.Solver.Headers.SlotNames

namespace InitECandidate.Solver.Headers.CurrentPipeline
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- Reached physical input/records, allocated output and actual live locals.
No completed header or future helper/store success is included. -/
structure State (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer array header current : BitVec 64) (bytes : Nat) (items : List Rlp.ListItem) (active : List Slot) : Prop where
  slices : CurrentHelpers.SliceImage source pointer array bytes items
  slots : Slots source active
  arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array))
  headerCell : source.locals.lookup (ofString "h")=some (.val (.word header))
  currentCell : source.locals.lookup (ofString "is_current")=some (.val (.word current))
  branch : (current=0#64 ∧ items.length=21) ∨ (current=1#64 ∧ items.length=23)
  headerArena : AllocatedBytes.Arena header 248
  headerAligned : header.toNat%8=0
  recordsBeforeHeader : array.toNat+16*items.length≤header.toNat
  heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded header 248#64)))

theorem State.of_parts {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer array header current : BitVec 64} {bytes : Nat} {items : List Rlp.ListItem} {active : List Slot}
    (data : State source pointer array header current bytes items active) (nextActive : List Slot)
    (slices : CurrentHelpers.SliceImage target pointer array bytes items) (slots : Slots target nextActive)
    (globals : target.globals=source.globals)
    (arrayCell : target.locals.lookup (ofString "arr")=some (.val (.word array)))
    (headerCell : target.locals.lookup (ofString "h")=some (.val (.word header)))
    (currentCell : target.locals.lookup (ofString "is_current")=some (.val (.word current))) :
    State target pointer array header current bytes items nextActive :=
  ⟨slices,slots,arrayCell,headerCell,currentCell,data.branch,data.headerArena,data.headerAligned,data.recordsBeforeHeader,
    by rw [globals]; exact data.heap⟩

/-- A real checked helper return supplies its shape and full frame before
entering the original lexical scope; earlier actual slot types survive. -/
theorem State.resume {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer array header current : BitVec 64} {bytes rowBytes : Nat} {items : List Rlp.ListItem} {active : List Slot}
    (data : State source pointer array header current bytes items active) (kind : Helper.Kind)
    (returned : CurrentHelpers.Returned source target kind rowBytes)
    (slot : Slot) (value : ValueHOL 64) (shape : shapeOfHOLExact value=slot.shape) :
    State (CallNormal.continuationEntry source target slot.text value) pointer array header current bytes items (slot::active) := by
  let ready:=CallNormal.continuationEntry source target slot.text value
  have frame : LocalEffects.erase ready=LocalEffects.erase source := returned.frame
  have slices:=data.slices.of_frame frame
  have baseSlots : Slots {target with locals:=source.locals} active := data.slots.of_locals source _ active rfl
  have slots : Slots ready (slot::active) := by
    change Slots (setVarHOLFinite (ofString slot.text) value {target with locals:=source.locals}) (slot::active)
    rw [slot.of_text]
    exact baseSlots.set _ active slot value shape
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  apply data.of_parts (slot::active) slices slots globals
  · simp [ready,CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_array,Ne.symm slot.not_array,data.arrayCell]
  · simp [ready,CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_header,Ne.symm slot.not_header,data.headerCell]
  · simp [ready,CallNormal.continuationEntry,setVarHOLFinite,slot.of_text,HolFiniteMapExact.update,FUPDATE,slot.not_current,Ne.symm slot.not_current,data.currentCell]

end InitECandidate.Solver.Headers.CurrentPipeline

#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.of_parts
#print axioms InitECandidate.Solver.Headers.CurrentPipeline.State.resume
