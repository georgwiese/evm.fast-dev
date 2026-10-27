import InitECandidate.Solver.Input.CurrentStartup.RecordEntry
import InitECandidate.Solver.Input.RequestOffsetsTrace
import InitECandidate.Solver.Input.RequestOffsetValues

namespace InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest
variable {decoderOrigin : DecoderOrigin}
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual main-derived request entry must pass its real three-offset
validator. All offset facts refer to original mathematical input bytes. -/
theorem offsets (input : Guest.InputBlob) (word : BitVec 64) (actual : RecordEntry.Reached (decoderOrigin := decoderOrigin) input word) :
    Guest.GasLimit.le32 input 18 = 44 ∧ 44 ≤ Guest.GasLimit.le32 input 22 ∧
      Guest.GasLimit.le32 input 22 ≤ Guest.GasLimit.le32 input 58 ∧
      Guest.GasLimit.le32 input 58 ≤ Guest.GasLimit.le32 input 6 - 16 := by
  obtain ⟨source, post, pointer, record, lengthBound, installed, shapes, domain, endian, image, heap,
    workspace, lower, aligned, room, recordLower, recordAligned, recordRoom, recordHeap, si, np, nlen, extent, requestLower, requestUpper, outer, rootFrame, returned⟩ := actual
  rcases Request.offsets_trace source post input pointer 2701132528#64 (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6 - 16))
    image extent np nlen workspace domain aligned (by decide) (by omega) (by decide)
    (by change 2701132528 + 64 ≤ pointer.toNat; omega)
    (CanonicalHeader.offset_code source.code installed) (CanonicalHeader.fail_code source.code installed) (shapes .SszErr)
    (some (.returned (.val (.word word)))) returned (by simp) with fault | continued
  · obtain ⟨error, allowed, impossible, paid⟩ := fault
    cases impossible
  · obtain ⟨first, valid, next, inner, paid, bound, funded, stateEq, retained, remaining, restored⟩ := continued
    have natural := Request.request_values input _ first valid
    have small := Framing.le32_lt input 6
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at natural
    exact natural

/-- Both canonical container offsets now derive from real normal decoder
execution, rather than being supplied as gas-decoding hypotheses. -/
theorem separated_offsets (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin) :
    Guest.GasLimit.le32 input 2 = 16 ∧ Guest.GasLimit.le32 input 18 = 44 := by
  have header := CanonicalHeader.separated_first input decoderOrigin.word actual.unroot
  have request := offsets input decoderOrigin.word (RecordEntry.separated input actual)
  exact ⟨header.2.2.2.1, request.1⟩

/-- The original declared-gas premise bounds the eight canonical input
bytes at474, after both actual offset guards. This is the raw byte field;
its actual later load/store still needs the payload-entry/image proof. -/
theorem gas_field (input : Guest.InputBlob)
    (actual : MainSeparatedInput.RootRun input decoderOrigin)
    (gas : Guest.GasLimit.declaredGasLimit input ≤ 200000000) :
    Guest.GasLimit.le64 input 474 ≤ 200000000 := by
  obtain ⟨first, second⟩ := separated_offsets input actual
  rw [Framing.declared_gas_at_474 input first second] at gas
  exact gas

end InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest

#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest.offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest.separated_offsets
#print axioms InitECandidate.Solver.Input.CurrentStartup.CanonicalRequest.gas_field
