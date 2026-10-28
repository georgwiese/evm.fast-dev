import InitECandidate.Solver.Input.PayloadRemainingImage
import InitECandidate.Solver.Input.PayloadTransactionFrame

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- Complete normally returned payload data used by the original hasher:
its actual physical cells/records and the passing offset/count arithmetic. -/
structure ReturnedImage (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record array : BitVec 64) (length start size : Nat) : Prop where
  transactions : TransactionImage input state pointer record array start size
  remaining : ∃ count, RemainingImage input state pointer record length count ∧
    count.toNat = (offsetWords input 3 - offsetWords input 2).toNat / 44 ∧
    (offsetWords input 3 - offsetWords input 2).toNat % 44 = 0
  valid : ∀ position < 4, Offsets.ValidAt 540#64 (BitVec.ofNat 64 length) (offsetWords input) position
  lengthEq : length = Guest.GasLimit.le32 input 22 - 44
  minimum : 540 ≤ length
  sliceUpper : length ≤ input.length % 2^64 - 62

theorem ReturnedImage.of_frame {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {length start size : Nat}
    (data : ReturnedImage input source pointer record array length start size)
    (frame : LocalEffects.erase target = LocalEffects.erase source) :
    ReturnedImage input target pointer record array length start size := by
  obtain ⟨count, cells, division, remainder⟩ := data.remaining
  exact ⟨data.transactions.of_frame frame, ⟨count, cells.of_frame frame, division, remainder⟩,
    data.valid, data.lengthEq, data.minimum, data.sliceUpper⟩

theorem ReturnedImage.of_interval {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {length start size : Nat}
    (data : ReturnedImage input source pointer record array length start size)
    (boundary : Nat) (before : array.toNat + 16 * VarList.decodedCount input start size ≤ boundary)
    (memory : ∀ query : BitVec 64, record.toNat ≤ query.toNat → query.toNat < boundary → target.memory query = source.memory query)
    (heap : NormalHeapEffects.AtLeast (array.toNat + 16 * VarList.decodedCount input start size) target) :
    ReturnedImage input target pointer record array length start size := by
  obtain ⟨count, cells, division, remainder⟩ := data.remaining
  have room : record.toNat + 136 ≤ 33806089496 := by
    obtain ⟨cursor, cell, low, high, aligned⟩ := data.transactions.heapExtent
    have := data.transactions.arrayAfter
    omega
  have after : record.toNat + 136 ≤ boundary := by have := data.transactions.arrayAfter; omega
  refine ⟨data.transactions.of_interval boundary before memory heap, ⟨count, cells.of_memory room ?_, division, remainder⟩,
    data.valid, data.lengthEq, data.minimum, data.sliceUpper⟩
  intro query lower upper
  exact memory query lower (by omega)

theorem ReturnedImage.store_before {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record array : BitVec 64} {length start size : Nat}
    (data : ReturnedImage input source pointer record array length start size)
    (destination word : BitVec 64) (before : destination.toNat < record.toNat) :
    ReturnedImage input {source with memory := WitnessRadix.StoreWord.put source.memory destination word}
      pointer record array length start size := by
  apply data.of_interval (array.toNat + 16 * VarList.decodedCount input start size) (Nat.le_refl _)
  · intro query lower upper
    have away : query ≠ destination := by intro same; rw [same] at lower; omega
    simp [WitnessRadix.StoreWord.put, away]
  · exact data.transactions.heapExtent

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.ReturnedImage.of_frame
#print axioms InitECandidate.Solver.Input.Payload.ReturnedImage.of_interval
#print axioms InitECandidate.Solver.Input.Payload.ReturnedImage.store_before
