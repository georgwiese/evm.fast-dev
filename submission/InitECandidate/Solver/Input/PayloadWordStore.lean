import InitECandidate.Solver.Input.PayloadTransactionsProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def fieldStored (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (offset : Nat) (value : BitVec 64) :=
  {source with memory:=WitnessRadix.StoreWord.put source.memory (cursor+BitVec.ofNat 64 offset) value}

theorem field_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (offset : Nat) (value : BitVec 64) :
    WitnessRadix.BackingLayout.control (fieldStored source cursor offset value)=WitnessRadix.BackingLayout.control source := rfl

theorem allocated_field_control (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor : BitVec 64) (offset : Nat)
    (value array amount : BitVec 64) :
    WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post (fieldStored source cursor offset value) array amount)=
      WitnessRadix.BackingLayout.control (WitnessRadix.PersistentAlloc.post source array amount) := rfl

/-- Every actual word field of the allocated 136-byte payload is mapped and
separate from the copied input. No clock or control field changes. -/
theorem field_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer cursor : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (pl : source.locals.lookup (ofString "pl")=some (.val (.word cursor)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496)
    (offset : Nat) (small : offset≤128) (offsetAligned : offset%8=0)
    (expression : ExpHOL 64) (value : BitVec 64)
    (read : eval source expression=some (.val (.word value))) :
    evaluateHOLFiniteState source (.store (Scalar.plus (localVar "pl") offset) expression)=
      (none,fieldStored source cursor offset value) ∧
      Blob.HeapInput (fieldStored source cursor offset value) input pointer ∧
      (fieldStored source cursor offset value).memory (cursor+BitVec.ofNat 64 offset)=.word value ∧
      (∀ query,query≠cursor+BitVec.ofNat 64 offset→(fieldStored source cursor offset value).memory query=source.memory query) := by
  classical
  have encoded : (BitVec.ofNat 64 offset).toNat=offset := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have number : (cursor+BitVec.ofNat 64 offset).toNat=cursor.toNat+offset := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]
  have mapped : source.memaddrs (cursor+BitVec.ofNat 64 offset) := by
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [number]; omega
    · rw [number]; omega
    · rw [number]; omega
  have address:=Scalar.plus_read source (localVar "pl") cursor offset (Request.local_word source "pl" cursor pl)
  refine ⟨WitnessRadix.StoreWord.execute source _ expression _ value address read mapped,?_,?_,?_⟩
  · exact Blob.HeapInput.store_separate source input pointer _ value heap pointerAligned (by omega)
      (Or.inr (by rw [number]; omega))
  · simp [fieldStored,WitnessRadix.StoreWord.put]
  · intro query away
    simp [fieldStored,WitnessRadix.StoreWord.put,away]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.field_store
#print axioms InitECandidate.Solver.Input.Payload.field_control
#print axioms InitECandidate.Solver.Input.Payload.allocated_field_control
