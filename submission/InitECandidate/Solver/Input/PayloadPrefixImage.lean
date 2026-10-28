import InitECandidate.Solver.Input.PayloadFields
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.Payload
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- The three early payload cells consumed by hashing, including the real
32-byte extra-data guard. Their addresses and lengths refer to copied input. -/
structure PrefixImage (input : Guest.InputBlob) (state : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) : Prop where
  raw : state.memory record = .word (pointer + 62#64)
  extraPointer : state.memory (record + 16#64) = .word (pointer + 602#64)
  extraLength : state.memory (record + 24#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 566 - 540))
  extraBound : Guest.GasLimit.le32 input 566 - 540 ≤ 32

theorem PrefixImage.of_memory {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer record : BitVec 64}
    (data : PrefixImage input source pointer record) (room : record.toNat + 136 ≤ 33806089496)
    (memory : ∀ query : BitVec 64, record.toNat ≤ query.toNat → query.toNat < record.toNat + 32 → target.memory query = source.memory query) :
    PrefixImage input target pointer record := by
  have number (offset : Nat) (small : offset ≤ 24) : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
    have encoded : (BitVec.ofNat 64 offset).toNat = offset := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega), encoded]
  refine ⟨(memory record (Nat.le_refl _) (by omega)).trans data.raw,
    (memory (record + 16#64) (by rw [number 16 (by decide)]; omega) (by rw [number 16 (by decide)]; omega)).trans data.extraPointer,
    (memory (record + 24#64) (by rw [number 24 (by decide)]; omega) (by rw [number 24 (by decide)]; omega)).trans data.extraLength,
    data.extraBound⟩

theorem PrefixImage.of_frame {input : Guest.InputBlob}
    {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer record : BitVec 64}
    (data : PrefixImage input source pointer record)
    (frame : LocalEffects.erase target = LocalEffects.erase source) : PrefixImage input target pointer record := by
  have memory := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => state.memory) frame
  change target.memory = source.memory at memory
  exact ⟨(congrArg (fun cells => cells record) memory).trans data.raw,
    (congrArg (fun cells => cells (record + 16#64)) memory).trans data.extraPointer,
    (congrArg (fun cells => cells (record + 24#64)) memory).trans data.extraLength, data.extraBound⟩

/-- Transaction and later payload writes begin at offset32, after this image. -/
theorem PrefixImage.store_after {input : Guest.InputBlob}
    {source : PanSemStateFiniteExact 64 Guest.HostMemory} {pointer record : BitVec 64}
    (data : PrefixImage input source pointer record) (offset : Nat) (word : BitVec 64)
    (lower : 32 ≤ offset) (upper : offset ≤ 128) (room : record.toNat + 136 ≤ 33806089496) :
    PrefixImage input (fieldStored source record offset word) pointer record := by
  apply data.of_memory room
  intro query after before
  have encoded : (BitVec.ofNat 64 offset).toNat = offset := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have number : (record + BitVec.ofNat 64 offset).toNat = record.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [encoded]; omega), encoded]
  have away : query ≠ record + BitVec.ofNat 64 offset := by
    intro same
    rw [same, number] at before
    omega
  simp [fieldStored, WitnessRadix.StoreWord.put, away]

end InitECandidate.Solver.Input.Payload

#print axioms InitECandidate.Solver.Input.Payload.PrefixImage.of_memory
#print axioms InitECandidate.Solver.Input.Payload.PrefixImage.of_frame
#print axioms InitECandidate.Solver.Input.Payload.PrefixImage.store_after
