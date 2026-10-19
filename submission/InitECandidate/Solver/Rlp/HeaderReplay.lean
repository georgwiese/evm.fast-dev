import InitECandidate.Solver.Rlp.HeaderEncodingNormal
import InitECandidate.Solver.Rlp.HeaderEncodingFrame
import InitECandidate.Solver.Rlp.UncheckedEncoding
import InitECandidate.Solver.Rlp.HeaderNormal

namespace InitECandidate.Solver.Rlp.Header
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem Valid.result_fields (length : Nat) (header payload flag : BitVec 64)
    (valid : Valid length (result header payload flag)) :
    header.toNat≤9 ∧ 1≤header.toNat+payload.toNat ∧ header.toNat+payload.toNat≤length ∧
      (flag=0#64 ∨ flag=1#64) ∧ (flag=1#64 → 1≤header.toNat) := by
  obtain ⟨actualHeader,actualPayload,actualFlag,same,head,positive,bounded,binary,listHead⟩ := valid
  have fields : header=actualHeader ∧ payload=actualPayload ∧ flag=actualFlag := by
    simpa [result] using same
  rcases fields with ⟨rfl,rfl,rfl⟩
  exact ⟨head,positive,bounded,binary,listHead⟩

/-- The original unchecked second pass recovers exactly the positive
bounded size established by an actual validated first pass on the same
input bytes. Clocks and unrelated state may differ. -/
theorem unchecked_replay (source target sourcePost targetPost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length : BitVec 64) (validatedValue uncheckedValue : ValueHOL 64)
    (sourcePointer : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (sourceLength : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (targetPointer : target.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (sourceInstalled : Input.OriginalCode.Installed source.code) (targetInstalled : Input.OriginalCode.Installed target.code)
    (bytes : ReadLength.BytesAgree source target pointer length)
    (validated : evaluateHOLFiniteState source body=(some (.returned validatedValue),sourcePost))
    (unchecked : evaluateHOLFiniteState target Unchecked.body=(some (.returned uncheckedValue),targetPost)) :
    ∃ header payload flag : BitVec 64,validatedValue=result header payload flag ∧
      uncheckedValue=.val (.word (header+payload)) ∧ 1≤(header+payload).toNat ∧ (header+payload).toNat≤length.toNat := by
  obtain ⟨header,payload,flag,encoding,answer⟩ := body_encoding source sourcePost pointer sourcePointer sourceInstalled validatedValue validated
  have valid := body_returns source length sourceLength sourceInstalled sourcePost validatedValue validated
  rw [answer] at valid
  obtain ⟨head,positive,bounded,binary,listHead⟩ := Valid.result_fields length.toNat header payload flag valid
  have footprint : max 1 header.toNat≤length.toNat := by omega
  have transported := Encoded.transport source target pointer header payload flag encoding
    (fun offset inside=>bytes offset (by omega))
  obtain ⟨actualHeader,actualPayload,actualFlag,actualEncoding,actualAnswer⟩ :=
    Unchecked.body_encoding target targetPost pointer targetPointer targetInstalled uncheckedValue unchecked
  obtain ⟨headEq,payloadEq,flagEq⟩ := Encoded.unique target pointer header payload flag actualHeader actualPayload actualFlag transported actualEncoding
  rw [←headEq,←payloadEq] at actualAnswer
  have number : (header+payload).toNat=header.toNat+payload.toNat := BitVec.toNat_add_of_lt (by have := length.isLt; omega)
  exact ⟨header,payload,flag,answer,actualAnswer,by rw [number]; exact positive,by rw [number]; exact bounded⟩

end InitECandidate.Solver.Rlp.Header

#print axioms InitECandidate.Solver.Rlp.Header.Valid.result_fields
#print axioms InitECandidate.Solver.Rlp.Header.unchecked_replay
