import InitECandidate.Solver.Input.RequestOffsetsStores
import InitECandidate.Solver.Input.PayloadPrefixProgram
import InitECandidate.Solver.Input.HeapFlatScalar

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem header_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length : BitVec 64) (heap : Blob.HeapInput source input pointer)
    (p : source.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))))
    (n : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (cursorAligned : cursor.toNat%8=0)
    (pointerLower : 2701131776≤pointer.toNat)
    (cursorAfter : pointer.toNat+input.length%2^64+8≤cursor.toNat)
    (cursorRoom : cursor.toNat+136≤33806089496) :
    evaluateHOLFiniteState (allocated source cursor) pointerStore=(none,pointerStored source pointer cursor) ∧
    evaluateHOLFiniteState (pointerStored source pointer cursor) lengthStore=(none,headerStored source pointer cursor length) ∧
    Blob.HeapInput (headerStored source pointer cursor length) input pointer ∧
    (headerStored source pointer cursor length).memory cursor=.word (pointer+62#64) ∧
    (headerStored source pointer cursor length).memory (cursor+8#64)=.word length := by
  classical
  let entry:=allocated source cursor
  have pl : entry.locals.lookup (ofString "pl")=some (.val (.word cursor)) := bind_lookup_same _ _ _
  have savedP : entry.locals.lookup (ofString "p")=some (.val (.word (pointer+62#64))) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "p" cursor (by decide)).trans p
  have savedN : (pointerStored source pointer cursor).locals.lookup (ofString "len")=some (.val (.word length)) :=
    (bind_lookup_other (WitnessRadix.PersistentAlloc.post {source with clock:=source.clock-1} cursor 136#64) "pl" "len" cursor (by decide)).trans n
  have baseRead:=Request.local_word entry "pl" cursor pl
  have address0 : eval entry (Scalar.plus (localVar "pl") 0)=some (.val (.word cursor)) := by
    simpa using Scalar.plus_read entry (localVar "pl") cursor 0 baseRead
  have pRead:=Request.local_word entry "p" (pointer+62#64) savedP
  have nextPl : (pointerStored source pointer cursor).locals.lookup (ofString "pl")=some (.val (.word cursor)) := pl
  have address8:=Scalar.plus_read (pointerStored source pointer cursor) (localVar "pl") cursor 8
    (Request.local_word _ "pl" cursor nextPl)
  have nRead:=Request.local_word (pointerStored source pointer cursor) "len" length savedN
  have nextNumber : (cursor+8#64).toNat=cursor.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change cursor.toNat+8<2^64; omega)]
    rfl
  have mapped0 : entry.memaddrs cursor := by
    change source.memaddrs cursor
    rw [domain]
    exact WitnessRadix.BackingLayout.ordinary_mapped cursor (by omega) (by omega) cursorAligned
  have mapped8 : (pointerStored source pointer cursor).memaddrs (cursor+8#64) := by
    change source.memaddrs (cursor+8#64)
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [nextNumber]; omega
    · rw [nextNumber]; omega
    · rw [nextNumber]; omega
  have s0 : evaluateHOLFiniteState entry pointerStore=(none,pointerStored source pointer cursor) :=
    WitnessRadix.StoreWord.execute entry (Scalar.plus (localVar "pl") 0) (localVar "p") cursor (pointer+62#64) address0 pRead mapped0
  have s1 : evaluateHOLFiniteState (pointerStored source pointer cursor) lengthStore=(none,headerStored source pointer cursor length) :=
    WitnessRadix.StoreWord.execute (pointerStored source pointer cursor) (Scalar.plus (localVar "pl") 8) (localVar "len") (cursor+8#64) length address8 nRead mapped8
  have entryHeap : Blob.HeapInput entry input pointer := Blob.HeapInput.of_fields source entry input pointer rfl rfl rfl heap
  have firstHeap : Blob.HeapInput (pointerStored source pointer cursor) input pointer :=
    Blob.HeapInput.store_separate entry input pointer cursor (pointer+62#64) entryHeap pointerAligned (by omega) (Or.inr (by omega))
  have secondHeap : Blob.HeapInput (headerStored source pointer cursor length) input pointer :=
    Blob.HeapInput.store_separate (pointerStored source pointer cursor) input pointer (cursor+8#64) length firstHeap pointerAligned (by omega)
      (Or.inr (by rw [nextNumber]; omega))
  have different : cursor≠cursor+8#64 := by
    intro equal
    have h:=congrArg BitVec.toNat equal
    rw [nextNumber] at h
    omega
  refine ⟨s0,s1,secondHeap,?_,?_⟩
  · simp [headerStored,pointerStored,WitnessRadix.StoreWord.put,different]
  · simp [headerStored,WitnessRadix.StoreWord.put]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.header_stores
