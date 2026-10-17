import InitECandidate.Solver.Input.RequestOffsetsProgram

namespace InitECandidate.Solver.Input.Request
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem local_word (source : PanSemStateFiniteExact 64 Guest.HostMemory) (name : String) (word : BitVec 64)
    (present : source.locals.lookup (ofString name)=some (.val (.word word))) :
    eval source (localVar name)=some (.val (.word word)) := by
  simpa [eval,localVar,evalHOLExact,toExact] using present

theorem offsets_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (word : BitVec 64)
    (present : source.globals.lookup (ofString "ssz_offs")=some (.val (.word word))) :
    eval source Header.offsets=some (.val (.word word)) := by
  simpa [eval,Header.offsets,evalHOLExact,toExact] using present

theorem offsets_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat) :
    evaluateHOLFiniteState (offsetLoaded source input) storePayload=(none,payloadStored source input array) ∧
    evaluateHOLFiniteState (payloadStored source input array) storeHashes=(none,hashesStored source input array) ∧
    evaluateHOLFiniteState (hashesStored source input array) storeRequests=(none,offsetsStored source input array) ∧
    Blob.HeapInput (offsetsStored source input array) input pointer ∧
    (∀ position<3,source.memaddrs (array+BitVec.ofNat 64 (8*position))) ∧
    (∀ position<3,(offsetsStored source input array).memory (array+BitVec.ofNat 64 (8*position))=.word (requestWords input position)) := by
  classical
  have natural : ∀ offset≤16,(array+BitVec.ofNat 64 offset).toNat=array.toNat+offset := by
    intro offset small
    have encoded : (BitVec.ofNat 64 offset).toNat=offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]
  have mapped : ∀ position<3,source.memaddrs (array+BitVec.ofNat 64 (8*position)) := by
    intro position small
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [natural _ (by omega)]; omega
    · rw [natural _ (by omega)]; omega
    · rw [natural _ (by omega)]
      omega
  have a0 : source.memaddrs array := by simpa using mapped 0 (by decide)
  have a8 : source.memaddrs (array+8#64) := mapped 1 (by decide)
  have a16 : source.memaddrs (array+16#64) := mapped 2 (by decide)
  have r0:=offsets_global (offsetLoaded source input) array arrayGlobal
  have r8:=Scalar.plus_read (payloadStored source input array) Header.offsets array 8 (offsets_global _ array arrayGlobal)
  have r16:=Scalar.plus_read (hashesStored source input array) Header.offsets array 16 (offsets_global _ array arrayGlobal)
  have l0 : (offsetLoaded source input).locals.lookup (ofString "o_pl")=some (.val (.word (requestWords input 0))) :=
    (bind_lookup_other (offsetSecond source input) "o_rq" "o_pl" _ (by decide)).trans
      ((bind_lookup_other (offsetFirst source input) "o_vh" "o_pl" _ (by decide)).trans (bind_lookup_same _ _ _))
  have l1 : (payloadStored source input array).locals.lookup (ofString "o_vh")=some (.val (.word (requestWords input 1))) :=
    (bind_lookup_other (offsetSecond source input) "o_rq" "o_vh" _ (by decide)).trans (bind_lookup_same _ _ _)
  have l2 : (hashesStored source input array).locals.lookup (ofString "o_rq")=some (.val (.word (requestWords input 2))) := bind_lookup_same _ _ _
  have v0:=local_word (offsetLoaded source input) "o_pl" (requestWords input 0) l0
  have v1:=local_word (payloadStored source input array) "o_vh" (requestWords input 1) l1
  have v2:=local_word (hashesStored source input array) "o_rq" (requestWords input 2) l2
  have s0 : evaluateHOLFiniteState (offsetLoaded source input) storePayload=(none,payloadStored source input array) :=
    WitnessRadix.StoreWord.execute (offsetLoaded source input) Header.offsets (localVar "o_pl") array (requestWords input 0) r0 v0 a0
  have s1 : evaluateHOLFiniteState (payloadStored source input array) storeHashes=(none,hashesStored source input array) :=
    WitnessRadix.StoreWord.execute (payloadStored source input array) (Scalar.plus Header.offsets 8) (localVar "o_vh") (array+8#64) (requestWords input 1) r8 v1 a8
  have s2 : evaluateHOLFiniteState (hashesStored source input array) storeRequests=(none,offsetsStored source input array) :=
    WitnessRadix.StoreWord.execute (hashesStored source input array) (Scalar.plus Header.offsets 16) (localVar "o_rq") (array+16#64) (requestWords input 2) r16 v2 a16
  have loadedHeap : Blob.HeapInput (offsetLoaded source input) input pointer := heap
  have h0 : Blob.HeapInput (payloadStored source input array) input pointer :=
    Blob.HeapInput.store_separate (offsetLoaded source input) input pointer array _ loadedHeap pointerAligned (by omega) (Or.inl (by omega))
  have h1 : Blob.HeapInput (hashesStored source input array) input pointer :=
    Blob.HeapInput.store_separate (payloadStored source input array) input pointer (array+8#64) _ h0 pointerAligned (by omega)
      (Or.inl (by rw [natural 8 (by decide)]; omega))
  have h2 : Blob.HeapInput (offsetsStored source input array) input pointer :=
    Blob.HeapInput.store_separate (hashesStored source input array) input pointer (array+16#64) _ h1 pointerAligned (by omega)
      (Or.inl (by rw [natural 16 (by decide)]; omega))
  have diff08 : array≠array+8#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 8 (by decide)] at h
    omega
  have diff016 : array≠array+16#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 16 (by decide)] at h
    omega
  have diff816 : array+8#64≠array+16#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 8 (by decide),natural 16 (by decide)] at h
    omega
  refine ⟨s0,s1,s2,h2,mapped,?_⟩
  intro position small
  have cases : position=0 ∨ position=1 ∨ position=2 := by omega
  rcases cases with rfl|rfl|rfl <;>
    simp [offsetsStored,hashesStored,payloadStored,WitnessRadix.StoreWord.put,diff08,diff016,diff816]

end InitECandidate.Solver.Input.Request

#print axioms InitECandidate.Solver.Input.Request.offsets_stores

#print axioms InitECandidate.Solver.Input.Request.local_word
#print axioms InitECandidate.Solver.Input.Request.offsets_global
