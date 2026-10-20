import InitECandidate.Solver.Input.MainPayloadSetup
import InitECandidate.Solver.Input.DecoderRuntimeCode
import InitECandidate.Solver.Input.PayloadPassingEntry

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Complete actual original payload normal return at any clock budget,
with all entry/runtime/room facts derived from main's reached callee. This
includes both decoded lists and every payload store. The real gas word is
bounded by the challenge premise; no future return or funding is assumed. -/
theorem normal_payload (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (layout : DecoderCall.RequestLayout input) (bounded : input.length % 2^64 ≤ Guest.maxInputBytes)
    (extent : 602 ≤ input.length % 2^64) (minimum : 540 ≤ Guest.GasLimit.le32 input 22 - 44)
    (sliceUpper : Guest.GasLimit.le32 input 22 - 44 ≤ input.length % 2^64 - 62)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState entry Payload.afterGuard = (some (.returned value),post)) :
    value = .val (.word (cursor input)) ∧
      post.memory (cursor input + 88#64) = .word (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)) ∧
      (BitVec.ofNat 64 (Guest.GasLimit.le64 input 474)).toNat ≤ 200000000 ∧
      post.memory (cursor input + 56#64) = .word (BitVec.ofNat 64 (Payload.withdrawalCount input)) ∧
      Blob.HeapInput post input inputPointer ∧ entry.clock - post.clock ≤ (input.length % 2^64) / 4 + 75 ∧
      entry.clock - post.clock ≤ 33554503 ∧ source.clock - post.clock ≤ (input.length % 2^64) / 4 + 86 ∧ post.clock ≤ entry.clock := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input ≤ 2847949152 := geometry.2.1
  have number := cursor_number input bounded
  have lengthNumber : (length input).toNat = Guest.GasLimit.le32 input 22 - 44 := by
    have small : input.length % 2^64 < 2^64 := Nat.mod_lt _ (by decide)
    rw [length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have installed : OriginalCode.Installed entry.code := actual.frame.code.symm ▸ environment.code
  have heapGlobal : entry.globals.lookup (ofString "heap_ptr") = some (.val (.word (cursor input))) := by
    rw [actual.frame.globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,cursor]
  have offsets : entry.globals.lookup (ofString "ssz_offs") = some (.val (.word 2713715344#64)) := by
    rw [actual.frame.globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr" == ofString "ssz_offs") = false from by decide] using environment.offsets
  have inside : 62 + (length input).toNat ≤ input.length % 2^64 := by rw [lengthNumber]; omega
  have room : (cursor input).toNat + 136 + 4 * (input.length % 2^64) ≤ 33806089496 := by
    have bound : input.length % 2^64 ≤ 134217712 := bounded
    rw [number.1]
    omega
  have whole : evaluateHOLFiniteState entry Payload.body = (some (.returned value),post) :=
    (Payload.passing_entry entry (length input) actual.length (by rw [lengthNumber]; exact minimum)).trans run
  obtain ⟨returned,gasCell,bytes,cost,forward,countCell⟩ := Payload.body_normal_any_clock entry post input inputPointer (cursor input) (length input) actual.bytes actual.pointer actual.length inside
    (actual.frame.domain.trans environment.domain) (by decide) number.2 (by decide)
    (by rw [number.1]; change 2713731432 + input.length % 2^64 + 8 ≤ DecoderSetup.cursor input + 384; omega) room heapGlobal
    (PersistentAlloc.original_code entry.code installed) 2713715344#64 offsets (by decide) (by decide) (by decide)
    (DecoderCall.original_offsets_code entry.code installed) (DecoderRuntime.division_code entry.code installed) (DecoderCall.original_fail_code entry.code installed)
    (by rw [actual.frame.exceptions]; exact environment.shapes .SszErr) (DecoderRuntime.var_list_code entry.code installed) (DecoderRuntime.fixed_list_code entry.code installed) value whole
  have uniform : (input.length % 2^64) / 4 + 75 ≤ 33554503 := by
    have bound : input.length % 2^64 ≤ 134217712 := bounded
    omega
  have before := actual.frame.clockLower
  have entryForward := actual.frame.forward
  exact ⟨returned,gasCell,Payload.stored_gas_bound input layout.outerFixed layout.requestFixed gas,countCell,bytes,cost,Nat.le_trans cost uniform,by omega,forward⟩

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.normal_payload
