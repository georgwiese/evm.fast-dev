import InitECandidate.Solver.Input.MainPayloadNormal
import InitECandidate.Solver.Input.PayloadImageAnyClock

namespace InitECandidate.Solver.Input.Main.PayloadPrefix
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Full physical original payload data at main's actual reached callee,
including the transaction record array and unchanged readonly/FFI context.
No budget, decoded-list validity or future continuation is assumed. -/
theorem normal_payload_image (input : Guest.InputBlob) (source entry post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (environment : DecoderCall.Environment input source) (actual : DecoderCall.PayloadEntry input source entry)
    (bounded : input.length%2^64≤Guest.maxInputBytes) (extent : 602≤input.length%2^64)
    (inside : 62+(length input).toNat≤input.length%2^64)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState entry Payload.afterGuard=(some (.returned value),post)) :
    Payload.Image post input inputPointer (cursor input) (length input) (PersistentAlloc.rounded (cursor input) 136#64) ∧
      VarList.Records post input inputPointer (PersistentAlloc.rounded (cursor input) 136#64) (62+Guest.GasLimit.le32 input 566) (Payload.transactionBytes input) ∧
      InitializerAllocations.context post=InitializerAllocations.context entry := by
  have geometry := input_cursor_bounds input bounded
  have lower : 2713731432+input.length%2^64+8≤DecoderSetup.cursor input := geometry.1
  have upper : DecoderSetup.cursor input≤2847949152 := geometry.2.1
  have number := cursor_number input bounded
  have small : input.length%2^64≤134217712 := bounded
  have installed : OriginalCode.Installed entry.code := actual.frame.code.symm ▸ environment.code
  have heap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor input))) := by
    rw [actual.frame.globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,cursor]
  have offsets : entry.globals.lookup (ofString "ssz_offs")=some (.val (.word 2713715344#64)) := by
    rw [actual.frame.globals]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show (ofString "heap_ptr"==ofString "ssz_offs")=false from by decide] using environment.offsets
  have after : inputPointer.toNat+input.length%2^64+8≤(cursor input).toNat := by
    change 2713731432+input.length%2^64+8≤_
    rw [number.1]
    omega
  have room : (cursor input).toNat+136+4*(input.length%2^64)≤33806089496 := by rw [number.1]; omega
  exact Payload.allocated_image_any_clock entry post input inputPointer (cursor input) (length input) actual.bytes extent actual.pointer actual.length inside
    (actual.frame.domain.trans environment.domain) (by decide) number.2 (by decide) after room heap (PersistentAlloc.original_code entry.code installed)
    2713715344#64 offsets (by decide) (by decide) (by decide) (DecoderCall.original_offsets_code entry.code installed) (DecoderRuntime.division_code entry.code installed)
    (DecoderCall.original_fail_code entry.code installed) (by rw [actual.frame.exceptions]; exact environment.shapes .SszErr) (DecoderRuntime.var_list_code entry.code installed)
    (DecoderRuntime.fixed_list_code entry.code installed) value run

end InitECandidate.Solver.Input.Main.PayloadPrefix

#print axioms InitECandidate.Solver.Input.Main.PayloadPrefix.normal_payload_image
