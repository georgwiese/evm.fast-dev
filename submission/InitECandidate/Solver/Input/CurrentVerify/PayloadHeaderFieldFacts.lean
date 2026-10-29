import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderInputSpans
import InitECandidate.Solver.Input.HeaderEncoding.FieldData

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Every encoder field is justified by the actual completed header and
its borrowed/fresh byte spans. No encoded result or future call is assumed. -/
theorem header_field_facts {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat} (words : RlpWrite.U256Value.Words)
    (data : Data input source pointer si record gasWord boundary) (buffers : HeaderBuffers heap)
    (memory : WordWrites.Memory)
    (cells : ∀ slot : Fin 31,memory (heap+BitVec.ofNat 64 (8*slot.val))=.word (headerWord source pointer record heap words slot)) :
    (∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts memory heap field) ∧
      (∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts memory heap field) := by
  have inputs:=input_spans data
  have read (slot : Fin 31) : HeaderEncoding.wordAt memory (HeaderEncoding.address heap (8*slot.val))=headerWord source pointer record heap words slot:=by
    change MemoryBytes.wordBits (memory (heap+BitVec.ofNat 64 (8*slot.val)))=_
    rw [cells]
    rfl
  have pointerFact (slot : Fin 31) (length : Nat) (owned : AllocatedBytes.Arena (headerWord source pointer record heap words slot) length)
      (small : length≤256) : HeaderEncoding.FieldFacts memory heap (.bytes (8*slot.val) length):=by
    refine ⟨by have bound:=slot.isLt; omega,by omega,small,?_⟩
    rw [read]
    exact owned
  have rawPart (offset length : Nat) (inside : offset+length≤540) : AllocatedBytes.Arena (pointer+62#64+BitVec.ofNat 64 offset) length:=inputs.raw_part offset length inside
  let extraLength:=Guest.GasLimit.le32 input 566-540
  have extraPointer : HeaderEncoding.wordAt memory (HeaderEncoding.address heap 128)=pointer+602#64:=by
    have value:=read 16
    change HeaderEncoding.wordAt memory (HeaderEncoding.address heap 128)=inputWord source record 16 at value
    exact value.trans inputs.extraPointer
  have extraSize : HeaderEncoding.wordAt memory (HeaderEncoding.address heap 136)=BitVec.ofNat 64 extraLength:=by
    have value:=read 17
    change HeaderEncoding.wordAt memory (HeaderEncoding.address heap 136)=inputWord source record 24 at value
    exact value.trans inputs.extraLength
  have small:=inputs.extraShort
  have lengthNumber : (BitVec.ofNat 64 extraLength).toNat=extraLength:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by dsimp [extraLength]; omega)]
  have extraFact : HeaderEncoding.FieldFacts memory heap .extra:=by
    change _≤32 ∧ _
    rw [extraPointer,extraSize,lengthNumber]
    exact ⟨small,inputs.extra⟩
  constructor
  · intro field member
    simp only [HeaderEncoding.firstField,HeaderEncoding.baseRest,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact pointerFact 1 32 (by simpa [headerWord,headerWords] using rawPart 0 32 (by decide)) (by decide)
    · exact pointerFact 2 32 buffers.ommer.ommerArena (by decide)
    · exact pointerFact 3 20 (rawPart 32 20 (by decide)) (by decide)
    · exact pointerFact 4 32 (rawPart 52 32 (by decide)) (by decide)
    · exact pointerFact 5 32 buffers.transactions (by decide)
    · exact pointerFact 6 32 (rawPart 84 32 (by decide)) (by decide)
    · exact pointerFact 7 256 (rawPart 116 256 (by decide)) (by decide)
    · exact ⟨by decide,by decide⟩
    · exact ⟨by decide,by decide⟩
    · exact ⟨by decide,by decide⟩
    · exact ⟨by decide,by decide⟩
    · exact ⟨by decide,by decide⟩
    · exact extraFact
    · exact pointerFact 18 32 (rawPart 372 32 (by decide)) (by decide)
    · exact pointerFact 19 8 buffers.nonce (by decide)
    · exact ⟨by decide,by decide⟩
    · exact pointerFact 24 32 buffers.withdrawals (by decide)
    · exact ⟨by decide,by decide⟩
    · exact ⟨by decide,by decide⟩
    · exact pointerFact 27 32 inputs.parent (by decide)
    · exact pointerFact 28 32 buffers.requests (by decide)
  · intro field member
    simp only [HeaderEncoding.optionalFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact pointerFact 29 32 buffers.balance (by decide)
    · exact ⟨by decide,by decide⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.header_field_facts
