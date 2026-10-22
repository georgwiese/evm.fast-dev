import InitECandidate.Solver.Input.PayloadHeaderFrame

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def inputWord (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (offset : Nat) : BitVec 64:=
  MemoryBytes.wordBits (source.memory (PayloadPrefix.cursor input+BitVec.ofNat 64 offset))

theorem HeaderFrame.input_frame (input : Guest.InputBlob) (origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (frame : HeaderFrame input source heap current)
    (original : HashInput.Frame origin source inputPointer.toNat root.toNat) (before : root.toNat≤heap.toNat) :
    HashInput.Frame origin current inputPointer.toNat root.toNat := by
  constructor
  intro query lower upper
  have low : 2713717616≤query.toNat:=by change 2713731432≤query.toNat at lower; omega
  exact (frame.older query low (by omega)).trans (original.words query lower upper)

/-- Every real aligned scalar payload load remains readable, including
fields outside the earlier hashing description. Values are the actual
incoming words, not assumed decoded constants. -/
theorem HeaderFrame.payload_read (input : Guest.InputBlob) (origin source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (counts : Nat→BitVec 64) (frame : HeaderFrame input source heap current)
    (prepared : RequestRootHashData.Prepared input origin root counts) (before : root.toNat≤heap.toNat)
    (domain : source.memaddrs=InitE.ordinaryDomain) (offset : Nat) (inside : offset<136) (aligned : offset%8=0) :
    eval current (PayloadHash.fieldExpression offset)=some (.val (.word (inputWord input source offset))) := by
  have arena : AllocatedBytes.Arena (PayloadPrefix.cursor input) 136:=prepared.layout.payload.payloadArena
  have pointerAligned : (PayloadPrefix.cursor input).toNat%8=0:=prepared.layout.payload.payloadAligned
  have pointerLower : inputPointer.toNat≤(PayloadPrefix.cursor input).toNat:=prepared.layout.payload.payloadLower
  have pointerBefore : (PayloadPrefix.cursor input).toNat+136≤root.toNat:=prepared.layout.payload.payloadBefore
  have number:=byteAddress_toNat (PayloadPrefix.cursor input) offset (by have h:=arena.upper; omega)
  change (PayloadPrefix.cursor input+BitVec.ofNat 64 offset).toNat=(PayloadPrefix.cursor input).toNat+offset at number
  have mapped:=AllocatedBytes.word_mapped current (PayloadPrefix.cursor input) 136 offset (frame.domain.trans domain) arena inside pointerAligned aligned
  change current.memaddrs (PayloadPrefix.cursor input+BitVec.ofNat 64 offset) at mapped
  have same:=frame.older (PayloadPrefix.cursor input+BitVec.ofNat 64 offset)
    (by change 2713731432≤(PayloadPrefix.cursor input).toNat at pointerLower; omega) (by omega)
  have stored : source.memory (PayloadPrefix.cursor input+BitVec.ofNat 64 offset)=.word (inputWord input source offset):=by
    cases cell:source.memory (PayloadPrefix.cursor input+BitVec.ofNat 64 offset) with
    | word value=>simp [inputWord,cell,MemoryBytes.wordBits]
  have payload:=frame.payload
  simp [eval,evalHOLExact,evalListHOLExact,toExact,PayloadHash.fieldExpression,localVar,payload,
    valueIsWord,valueWord,wordOpHOL,wordOp,isWfShapeExactHOL,memLoadHOLExact,mapped,same,stored]

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.input_frame
#print axioms InitECandidate.Solver.Input.PayloadHeader.HeaderFrame.payload_read
