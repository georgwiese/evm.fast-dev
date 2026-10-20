import InitECandidate.Solver.Input.PayloadPreparedFacts

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes

/-- The exact original offset scratch writes preserve every later word. -/
theorem offsets_memory_after (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (array query : BitVec 64)
    (room : array.toNat+32<2^64) (after : array.toNat+32≤query.toNat) :
    (offsetsStored source input array).memory query=source.memory query := by
  have away (offset : Nat) (inside : offset<32) : query≠array+BitVec.ofNat 64 offset := by
    have address : (array+BitVec.ofNat 64 offset).toNat=array.toNat+offset := byteAddress_toNat array offset (by omega)
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address] at equal
    omega
  simp only [offsetsStored,withdrawalsStored,transactionsStored,extraStored,StoreWord.put,
    if_neg (away 24 (by decide)),if_neg (away 16 (by decide)),if_neg (away 8 (by decide)),if_neg (by simpa using away 0 (by decide))]

/-- The actual payload allocation/header/declaration template stores its two
header words, and all four later scratch writes leave those exact cells intact. -/
theorem prepared_header_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer cursor length array : BitVec 64) (room : cursor.toNat+136≤33806089496) (before : array.toNat+32≤cursor.toNat) :
    (offsetsStored (prepared source input pointer cursor length) input array).memory cursor=.word (pointer+62#64) ∧
    (offsetsStored (prepared source input pointer cursor length) input array).memory (cursor+8#64)=.word length := by
  have nextNumber : (cursor+8#64).toNat=cursor.toNat+8 := by
    rw [BitVec.toNat_add_of_lt (by change cursor.toNat+8<2^64; omega)]
    rfl
  have different : cursor≠cursor+8#64 := by intro same; have equal := congrArg BitVec.toNat same; rw [nextNumber] at equal; omega
  have preparedMemory : (prepared source input pointer cursor length).memory=(headerStored source pointer cursor length).memory := rfl
  rw [offsets_memory_after _ _ _ cursor (by omega) before,
    offsets_memory_after _ _ _ (cursor+8#64) (by omega) (by rw [nextNumber]; omega),preparedMemory]
  constructor
  · change StoreWord.put (StoreWord.put source.memory cursor (pointer+62#64)) (cursor+8#64) length cursor=_
    simp [StoreWord.put,different]
  · change StoreWord.put (StoreWord.put source.memory cursor (pointer+62#64)) (cursor+8#64) length (cursor+8#64)=_
    simp [StoreWord.put]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.offsets_memory_after
#print axioms InitECandidate.Solver.Input.Payload.prepared_header_cells
