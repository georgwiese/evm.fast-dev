import InitECandidate.Solver.Input.RequestOffsetsStores
import InitECandidate.Solver.Input.PayloadOffsetsProgram

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- All actual payload validator-array stores and their copied-input frame.
The four local words are established by the checked declaration prefix. -/
theorem offsets_stores (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer array : BitVec 64)
    (heap : Blob.HeapInput source input pointer)
    (arrayGlobal : source.globals.lookup (ofString "ssz_offs")=some (.val (.word array)))
    (l0 : source.locals.lookup (ofString "o_extra")=some (.val (.word (offsetWords input 0))))
    (l1 : source.locals.lookup (ofString "o_txs")=some (.val (.word (offsetWords input 1))))
    (l2 : source.locals.lookup (ofString "o_wd")=some (.val (.word (offsetWords input 2))))
    (l3 : source.locals.lookup (ofString "o_bal")=some (.val (.word (offsetWords input 3))))
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (pointerAligned : pointer.toNat%8=0) (arrayAligned : array.toNat%8=0)
    (upper : pointer.toNat+input.length%2^64+8≤33806089496)
    (arrayLower : 2701131776≤array.toNat) (arrayBefore : array.toNat+64≤pointer.toNat) :
    evaluateHOLFiniteState (source) storeExtra=(none,extraStored source input array) ∧
    evaluateHOLFiniteState (extraStored source input array) storeTransactions=(none,transactionsStored source input array) ∧
    evaluateHOLFiniteState (transactionsStored source input array) storeWithdrawals=(none,withdrawalsStored source input array) ∧
    evaluateHOLFiniteState (withdrawalsStored source input array) storeBalances=(none,offsetsStored source input array) ∧
    Blob.HeapInput (offsetsStored source input array) input pointer ∧
    (∀ position<4,source.memaddrs (array+BitVec.ofNat 64 (8*position))) ∧
    (∀ position<4,(offsetsStored source input array).memory (array+BitVec.ofNat 64 (8*position))=.word (offsetWords input position)) := by
  classical
  have natural : ∀ offset≤24,(array+BitVec.ofNat 64 offset).toNat=array.toNat+offset := by
    intro offset small
    have encoded : (BitVec.ofNat 64 offset).toNat=offset := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega),encoded]
  have mapped : ∀ position<4,source.memaddrs (array+BitVec.ofNat 64 (8*position)) := by
    intro position small
    rw [domain]
    apply WitnessRadix.BackingLayout.ordinary_mapped
    · rw [natural _ (by omega)]; omega
    · rw [natural _ (by omega)]; omega
    · rw [natural _ (by omega)]; omega
  have a0 : (source).memaddrs array := by simpa using mapped 0 (by decide)
  have r0:=Request.offsets_global source array arrayGlobal
  have v0:=Request.local_word (source) "o_extra" (offsetWords input 0) l0
  have s0 : evaluateHOLFiniteState (source) storeExtra=(none,extraStored source input array) :=
    WitnessRadix.StoreWord.execute (source) Header.offsets (localVar "o_extra") array (offsetWords input 0) r0 v0 a0
  have h0 : Blob.HeapInput (extraStored source input array) input pointer :=
    Blob.HeapInput.store_separate (source) input pointer array (offsetWords input 0) heap pointerAligned (by omega) (Or.inl (by omega))
  have a1 : (extraStored source input array).memaddrs (array+8#64) := by
    change source.memaddrs (array+8#64)
    exact mapped 1 (by decide)
  have r1:=Scalar.plus_read (extraStored source input array) Header.offsets array 8 (Request.offsets_global _ array arrayGlobal)
  have v1:=Request.local_word (extraStored source input array) "o_txs" (offsetWords input 1) l1
  have s1 : evaluateHOLFiniteState (extraStored source input array) storeTransactions=(none,transactionsStored source input array) :=
    WitnessRadix.StoreWord.execute (extraStored source input array) (Scalar.plus Header.offsets 8) (localVar "o_txs") (array+8#64) (offsetWords input 1) r1 v1 a1
  have h1 : Blob.HeapInput (transactionsStored source input array) input pointer :=
    Blob.HeapInput.store_separate (extraStored source input array) input pointer (array+8#64) (offsetWords input 1) h0 pointerAligned (by omega) (Or.inl (by rw [natural 8 (by decide)]; omega))
  have a2 : (transactionsStored source input array).memaddrs (array+16#64) := by
    change source.memaddrs (array+16#64)
    exact mapped 2 (by decide)
  have r2:=Scalar.plus_read (transactionsStored source input array) Header.offsets array 16 (Request.offsets_global _ array arrayGlobal)
  have v2:=Request.local_word (transactionsStored source input array) "o_wd" (offsetWords input 2) l2
  have s2 : evaluateHOLFiniteState (transactionsStored source input array) storeWithdrawals=(none,withdrawalsStored source input array) :=
    WitnessRadix.StoreWord.execute (transactionsStored source input array) (Scalar.plus Header.offsets 16) (localVar "o_wd") (array+16#64) (offsetWords input 2) r2 v2 a2
  have h2 : Blob.HeapInput (withdrawalsStored source input array) input pointer :=
    Blob.HeapInput.store_separate (transactionsStored source input array) input pointer (array+16#64) (offsetWords input 2) h1 pointerAligned (by omega) (Or.inl (by rw [natural 16 (by decide)]; omega))
  have a3 : (withdrawalsStored source input array).memaddrs (array+24#64) := by
    change source.memaddrs (array+24#64)
    exact mapped 3 (by decide)
  have r3:=Scalar.plus_read (withdrawalsStored source input array) Header.offsets array 24 (Request.offsets_global _ array arrayGlobal)
  have v3:=Request.local_word (withdrawalsStored source input array) "o_bal" (offsetWords input 3) l3
  have s3 : evaluateHOLFiniteState (withdrawalsStored source input array) storeBalances=(none,offsetsStored source input array) :=
    WitnessRadix.StoreWord.execute (withdrawalsStored source input array) (Scalar.plus Header.offsets 24) (localVar "o_bal") (array+24#64) (offsetWords input 3) r3 v3 a3
  have h3 : Blob.HeapInput (offsetsStored source input array) input pointer :=
    Blob.HeapInput.store_separate (withdrawalsStored source input array) input pointer (array+24#64) (offsetWords input 3) h2 pointerAligned (by omega) (Or.inl (by rw [natural 24 (by decide)]; omega))
  have d01 : array≠array+8#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 8 (by decide)] at h
    omega
  have d02 : array≠array+16#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 16 (by decide)] at h
    omega
  have d03 : array≠array+24#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 24 (by decide)] at h
    omega
  have d12 : array+8#64≠array+16#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 8 (by decide),natural 16 (by decide)] at h
    omega
  have d13 : array+8#64≠array+24#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 8 (by decide),natural 24 (by decide)] at h
    omega
  have d23 : array+16#64≠array+24#64 := by
    intro eq
    have h:=congrArg BitVec.toNat eq
    rw [natural 16 (by decide),natural 24 (by decide)] at h
    omega
  refine ⟨s0,s1,s2,s3,h3,mapped,?_⟩
  intro position small
  have alternatives : position=0 ∨ position=1 ∨ position=2 ∨ position=3 := by omega
  rcases alternatives with rfl|rfl|rfl|rfl <;>
    simp [offsetsStored,withdrawalsStored,transactionsStored,extraStored,WitnessRadix.StoreWord.put,d01,d02,d03,d12,d13,d23]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.offsets_stores
