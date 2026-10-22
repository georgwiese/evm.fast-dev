import InitECandidate.Solver.Input.PayloadHeaderCells
import InitECandidate.Solver.Input.PayloadHeaderInputCells
import InitECandidate.Solver.Input.HeaderEncoding.Context

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix
open Main

/-- All encoder field premises follow from the actual header words and
main's decoded input layout. Every borrowed and fresh byte span is owned. -/
theorem header_field_facts (input : Guest.InputBlob) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root heap : BitVec 64) (counts : Nat→BitVec 64) (words : RlpWrite.U256Value.Words)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (originalFrame : HashInput.Frame origin source inputPointer.toNat root.toNat) (buffers : HeaderBuffers heap)
    (memory : WordWrites.Memory)
    (cells : ∀ slot : Fin 31,memory (heap+BitVec.ofNat 64 (8*slot.val))=.word (headerWord input source heap words slot)) :
    (∀ field∈HeaderEncoding.firstField::HeaderEncoding.baseRest,HeaderEncoding.FieldFacts memory heap field) ∧
      (∀ field∈HeaderEncoding.optionalFields,HeaderEncoding.FieldFacts memory heap field) := by
  have read (slot : Fin 31) : HeaderEncoding.wordAt memory (HeaderEncoding.address heap (8*slot.val))=headerWord input source heap words slot:=by
    change MemoryBytes.wordBits (memory (heap+BitVec.ofNat 64 (8*slot.val)))=_
    rw [cells]
    rfl
  have pointerFact (slot : Fin 31) (length : Nat) (owned : AllocatedBytes.Arena (headerWord input source heap words slot) length)
      (small : length≤256) : HeaderEncoding.FieldFacts memory heap (.bytes (8*slot.val) length):=by
    refine ⟨by have h:=slot.isLt; omega,by omega,small,?_⟩
    rw [read]
    exact owned
  have rawPart (offset length : Nat) (inside : offset+length≤540) :
      AllocatedBytes.Arena (inputPointer+62#64+BitVec.ofNat 64 offset) length:=
    AllocatedBytes.Arena.subrange _ 540 offset length prepared.layout.payload.rawArena inside
  let data:=PayloadHashData.description input
  have extraPointer : HeaderEncoding.wordAt memory (HeaderEncoding.address heap 128)=data.extra:=by
    have word:=input_word_of_image input origin source root counts prepared originalFrame (16,data.extra) (by simp [PayloadHash.Description.cells,data])
    simpa [headerWord,headerWords,word] using read 16
  have extraLength : HeaderEncoding.wordAt memory (HeaderEncoding.address heap 136)=BitVec.ofNat 64 data.extraLength:=by
    have word:=input_word_of_image input origin source root counts prepared originalFrame (24,BitVec.ofNat 64 data.extraLength) (by simp [PayloadHash.Description.cells,data])
    simpa [headerWord,headerWords,word] using read 17
  have extraShort : data.extraLength≤32:=prepared.layout.payload.extraShort
  have lengthNumber : (BitVec.ofNat 64 data.extraLength).toNat=data.extraLength:=by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have extraFact : HeaderEncoding.FieldFacts memory heap .extra:=by
    change _≤32 ∧ _
    rw [extraPointer,extraLength,lengthNumber]
    exact ⟨prepared.layout.payload.extraShort,prepared.layout.payload.extraArena⟩
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
    · exact pointerFact 27 32 prepared.layout.parentArena (by decide)
    · exact pointerFact 28 32 buffers.requests (by decide)
  · intro field member
    simp only [HeaderEncoding.optionalFields,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl
    · exact pointerFact 29 32 buffers.balance (by decide)
    · exact ⟨by decide,by decide⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.header_field_facts
