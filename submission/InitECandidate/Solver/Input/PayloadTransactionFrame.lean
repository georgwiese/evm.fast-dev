import InitECandidate.Solver.Input.PayloadTransactionImage
import InitECandidate.Solver.Input.VarList.RecordsIntervalFrame
import InitECandidate.Solver.WitnessRadix.StoreWord

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Moving the complete transaction image requires memory only on its actual
earlier record interval, and a genuine target heap frontier beyond the array. -/
theorem TransactionImage.of_interval {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {start size : Nat}
    (data : TransactionImage input source pointer record array start size)
    (boundary : Nat) (before : array.toNat + 16 * VarList.decodedCount input start size ≤ boundary)
    (memory : ∀ query : BitVec 64, record.toNat ≤ query.toNat → query.toNat < boundary → target.memory query = source.memory query)
    (heap : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) target) :
    TransactionImage input target pointer record array start size := by
  have room : record.toNat + 136 ≤ 2952790016 := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.heapExtent
    have := data.arrayAfter
    omega
  have number (offset : Nat) (small : offset ≤ 128) : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
    have encoded : (BitVec.ofNat 64 offset).toNat = offset := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega), encoded]
  refine ⟨data.startEq, data.sizeEq, data.inside, data.arrayAfter, heap, ?_, ?_, ?_⟩
  · apply VarList.Records.of_interval source target input pointer array start size boundary data.records before
    intro query lower upper
    exact memory query (by have := data.arrayAfter; omega) upper
  · exact (memory (record + 32#64) (by rw [number 32 (by decide)]; omega)
      (by rw [number 32 (by decide)]; have := data.arrayAfter; omega)).trans data.txs
  · exact (memory (record + 40#64) (by rw [number 40 (by decide)]; omega)
      (by rw [number 40 (by decide)]; have := data.arrayAfter; omega)).trans data.count

/-- A real earlier SI-field write cannot touch payload transaction data. -/
theorem TransactionImage.store_before {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {start size : Nat}
    (data : TransactionImage input source pointer record array start size)
    (destination word : BitVec 64) (before : destination.toNat < record.toNat) :
    TransactionImage input {source with memory := WitnessRadix.StoreWord.put source.memory destination word}
      pointer record array start size := by
  apply data.of_interval (array.toNat + 16 * VarList.decodedCount input start size) (Nat.le_refl _)
  · intro query lower upper
    have away : query ≠ destination := by intro same; rw [same] at lower; omega
    simp [WitnessRadix.StoreWord.put, away]
  · exact data.heapExtent

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.TransactionImage.of_interval
#print axioms InitECandidate.Solver.Input.Payload.TransactionImage.store_before
