import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderCells
import InitECandidate.Solver.Input.RawScalar

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The borrowed header strings are inside the same actual copied input.
The extra-data cells are the original decoded values, not arbitrary pointers. -/
structure InputSpans (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) : Prop where
  encodedMinimum : 602≤input.length%2^64
  raw : AllocatedBytes.Arena (pointer+62#64) 540
  parent : AllocatedBytes.Arena (pointer+26#64) 32
  extra : AllocatedBytes.Arena (pointer+602#64) (Guest.GasLimit.le32 input 566-540)
  extraShort : Guest.GasLimit.le32 input 566-540≤32
  extraPointer : inputWord source record 16=pointer+602#64
  extraLength : inputWord source record 24=BitVec.ofNat 64 (Guest.GasLimit.le32 input 566-540)

theorem input_spans {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat} (data : Data input source pointer si record gasWord boundary) :
    InputSpans input source pointer record := by
  obtain ⟨array,length,start,size,payload,before,count,bytes⟩:=data.payload
  have minimum:=payload.minimum
  have inputBefore:=payload.sliceUpper
  have encodedMinimum : 602≤input.length%2^64:=by omega
  have inputArena : AllocatedBytes.Arena pointer (input.length%2^64):=
    ⟨by have lower:=data.copied.lower; omega,by have before:=data.copied.beforeRecord; have upper:=data.recordArena.upper; omega⟩
  have extraLower : 540≤Guest.GasLimit.le32 input 566:=by
    have valid:=payload.valid 1 (by decide)
    change 540≤(BitVec.ofNat 64 (Guest.GasLimit.le32 input 566)).toNat ∧ _ at valid
    rw [RawScalar.le32_number] at valid
    exact valid.1
  have transactionStart:=payload.transactions.startEq
  have transactionInside:=payload.transactions.inside
  have extraInside : 602+(Guest.GasLimit.le32 input 566-540)≤input.length%2^64:=by omega
  exact ⟨encodedMinimum,
    inputArena.subrange pointer _ 62 540 (by omega),inputArena.subrange pointer _ 26 32 (by omega),
    inputArena.subrange pointer _ 602 _ extraInside,payload.transactions.hashPrefix.extraBound,
    congrArg MemoryBytes.wordBits payload.transactions.hashPrefix.extraPointer,
    congrArg MemoryBytes.wordBits payload.transactions.hashPrefix.extraLength⟩

/-- Every original borrowed raw subfield inherits the actual copied span. -/
theorem InputSpans.raw_part {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} (data : InputSpans input source pointer record) (offset length : Nat) (inside : offset+length≤540) :
    AllocatedBytes.Arena (pointer+62#64+BitVec.ofNat 64 offset) length:=
  data.raw.subrange _ 540 offset length inside

/-- Later block-length reads are below the actual temporary frontier:
input bytes, all transaction records and the four real payload cells. -/
theorem length_regions {input : Guest.InputBlob} {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat)
    (buffers : HeaderBuffers heap) :
    pointer.toNat+input.length%2^64≤(headerFrontier heap).toNat ∧
      (∀ array length start size,Payload.ReturnedImage input source pointer record array length start size→
        array.toNat+16*VarList.decodedCount input start size≤boundary→
        array.toNat+16*VarList.decodedCount input start size≤(headerFrontier heap).toNat) ∧
      (∀ offset∈([32,40,48,56] : List Nat),(record+BitVec.ofNat 64 offset).toNat<(headerFrontier heap).toNat) := by
  have frontier:=(buffers.numbers heap).frontier
  have inputBefore:=data.copied.beforeRecord
  have recordBefore:=data.recordInside.2
  refine ⟨by omega,?_,?_⟩
  · intro array length start size image bounded
    omega
  · intro offset member
    have inside : offset<136:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl <;> decide
    have number : (record+BitVec.ofNat 64 offset).toNat=record.toNat+offset:=byteAddress_toNat record offset (by have upper:=data.recordArena.upper; omega)
    rw [number]
    omega

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.input_spans
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.InputSpans.raw_part
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.length_regions
