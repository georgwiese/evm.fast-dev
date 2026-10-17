import InitECandidate.Solver.Input.PayloadWordStore

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

abbrev Field := Nat×ExpHOL 64×BitVec 64
def fieldProgram : List Field→ProgHOL 64
  | []=>.return (localVar "pl")
  | field::rest=>.seq (.store (Scalar.plus (localVar "pl") field.1) field.2.1) (fieldProgram rest)
def fieldMemory (memory : BitVec 64→HolWordLab 64) (cursor : BitVec 64) : List Field→BitVec 64→HolWordLab 64
  | []=>memory
  | field::rest=>fieldMemory (WitnessRadix.StoreWord.put memory (cursor+BitVec.ofNat 64 field.1) field.2.2) cursor rest
def applyFields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (fields : List Field) :=
  {source with memory:=fieldMemory source.memory cursor fields}

theorem applyFields_cons (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (field : Field) (rest : List Field) :
    applyFields source cursor (field::rest)=applyFields (fieldStored source cursor field.1 field.2.2) cursor rest := rfl

theorem applyFields_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (fields : List Field) :
    (applyFields source cursor fields).locals=source.locals := rfl

theorem applyFields_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (fields : List Field) :
    (applyFields source cursor fields).clock=source.clock := rfl

/-- Execute actual mapped payload stores and final pointer return, preserving
copied bytes. The read premise may use the established copied-input relation
at every intermediate state; it cannot assume unchanged memory. -/
theorem fields_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (fields : List Field) (valid : ∀ field∈fields,field.1≤128 ∧ field.1%8=0)
    (reads : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.locals=source.locals→Blob.HeapInput current input pointer→
      ∀ field∈fields,eval current field.2.1=some (.val (.word field.2.2))) :
    evaluateHOLFiniteState source (fieldProgram fields)=
      (some (.returned (.val (.word cursor))),emptyLocalsHOLFinite (applyFields source cursor fields)) ∧
    Blob.HeapInput (applyFields source cursor fields) input pointer := by
  induction fields generalizing source with
  | nil=>
    refine ⟨?_,heap⟩
    simp [fieldProgram,applyFields,fieldMemory,evaluateHOLFiniteState_return,evalHOLExact,toExact,localVar,pl,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  | cons field rest ih=>
    have firstValid:=valid field (by simp)
    obtain ⟨firstRun,firstHeap,firstCell,firstFrame⟩:=field_store source input pointer cursor heap pl domain pointerAligned cursorAligned
      pointerLower cursorAfter cursorRoom field.1 firstValid.1 firstValid.2 field.2.1 field.2.2 (reads source rfl heap field (by simp))
    let first:=fieldStored source cursor field.1 field.2.2
    have restValid : ∀ entry∈rest,entry.1≤128 ∧ entry.1%8=0 := fun entry mem=>valid entry (by simp [mem])
    have restReads : ∀ current : PanSemStateFiniteExact 64 Guest.HostMemory,current.locals=first.locals→Blob.HeapInput current input pointer→
        ∀ entry∈rest,eval current entry.2.1=some (.val (.word entry.2.2)) := by
      intro current localsEq currentHeap entry mem
      exact reads current localsEq currentHeap entry (by simp [mem])
    obtain ⟨tailRun,tailHeap⟩:=ih first firstHeap pl domain restValid restReads
    refine ⟨?_,tailHeap⟩
    rw [fieldProgram,WitnessRadix.StateSteps.next_sequence source first _ _ firstRun (Nat.le_refl _)]
    exact tailRun

theorem field_address_eq (cursor : BitVec 64) (room : cursor.toNat+136≤33806089496) (left right : Nat)
    (leftSmall : left≤128) (rightSmall : right≤128) :
    (cursor+BitVec.ofNat 64 left=cursor+BitVec.ofNat 64 right)↔left=right := by
  have number : ∀ offset≤128,(cursor+BitVec.ofNat 64 offset).toNat=cursor.toNat+offset := by
    intro offset small
    have encoded : (BitVec.ofNat 64 offset).toNat=offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]
  constructor
  · intro eq
    have natural:=congrArg BitVec.toNat eq
    rw [number left leftSmall,number right rightSmall] at natural
    omega
  · intro eq; rw [eq]

def cellValue : List Field→HolWordLab 64→Nat→HolWordLab 64
  | [],old,_=>old
  | field::rest,old,offset=>cellValue rest (if offset=field.1 then .word field.2.2 else old) offset

theorem applyFields_cell (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64)
    (room : cursor.toNat+136≤33806089496) (fields : List Field) (valid : ∀ field∈fields,field.1≤128)
    (offset : Nat) (small : offset≤128) :
    (applyFields source cursor fields).memory (cursor+BitVec.ofNat 64 offset)=
      cellValue fields (source.memory (cursor+BitVec.ofNat 64 offset)) offset := by
  induction fields generalizing source with
  | nil=>rfl
  | cons field rest ih=>
    rw [applyFields_cons,ih _ (by intro entry mem; exact valid entry (by simp [mem]))]
    simp only [cellValue,fieldStored,WitnessRadix.StoreWord.put,field_address_eq cursor room offset field.1 small (valid field (by simp))]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.fields_execute
#print axioms InitECandidate.Solver.Input.Payload.applyFields_cell
