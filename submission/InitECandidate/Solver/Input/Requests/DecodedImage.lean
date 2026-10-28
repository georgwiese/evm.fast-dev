import InitECandidate.Solver.Input.Requests.ImageLayout

namespace InitECandidate.Solver.Input.Requests
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Complete request decoder data at this physical state. It retains the
same actual slice, validated offsets, all ten cells and exact count arithmetic. -/
structure DecodedImage (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (blob cursor : BitVec 64) (start size : Nat) (counts : Nat→BitVec 64) : Prop where
  image : Image source (blob+BitVec.ofNat 64 start) cursor (BitVec.ofNat 64 size) (offsetWord input start) counts
  layout : Layout (offsetWord input start) (BitVec.ofNat 64 size)
  inside : start+size≤input.length%2^64
  minimum : 20≤size
  startEq : start=18+Guest.GasLimit.le32 input 58
  sizeEq : size=Guest.GasLimit.le32 input 6-16-Guest.GasLimit.le32 input 58
  inputArena : AllocatedBytes.Arena blob (input.length%2^64)
  inputBound : input.length%2^64≤251655056
  cursorArena : AllocatedBytes.Arena cursor 80
  cursorAligned : cursor.toNat%8=0
  cursorRoom : cursor.toNat+80≤2952790016
  inputLower : 2701134824≤blob.toNat
  cursorAfterInput : blob.toNat+input.length%2^64+8≤cursor.toNat

theorem DecodedImage.of_memory {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob cursor : BitVec 64} {start size : Nat} {counts : Nat→BitVec 64}
    (data : DecodedImage input source blob cursor start size counts)
    (frame : ∀ index<5, post.memory (cursor+BitVec.ofNat 64 (16*index))=source.memory (cursor+BitVec.ofNat 64 (16*index)) ∧
      post.memory (cursor+BitVec.ofNat 64 (16*index+8))=source.memory (cursor+BitVec.ofNat 64 (16*index+8))) : DecodedImage input post blob cursor start size counts :=
  ⟨data.image.of_memory frame,data.layout,data.inside,data.minimum,data.startEq,data.sizeEq,data.inputArena,data.inputBound,data.cursorArena,data.cursorAligned,data.cursorRoom,
    data.inputLower,data.cursorAfterInput⟩

end InitECandidate.Solver.Input.Requests

#print axioms InitECandidate.Solver.Input.Requests.DecodedImage.of_memory
