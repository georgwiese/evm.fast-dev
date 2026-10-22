import InitECandidate.Solver.Input.PayloadHeaderInputWords

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack PanSemStateFiniteExact WitnessRadix
open Main

/-- Recover a described decoded scalar directly from its actual old
record cell. The record image and memory agreement come from main. -/
theorem input_word_of_image (input : Guest.InputBlob) (origin source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root : BitVec 64) (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (frame : HashInput.Frame origin source inputPointer.toNat root.toNat)
    (cell : Nat×BitVec 64) (member : cell∈(PayloadHashData.description input).cells) :
    inputWord input source cell.1=cell.2 := by
  let data:=PayloadHashData.description input
  have valid:=data.cells_valid cell member
  have arena : AllocatedBytes.Arena data.payload 136:=prepared.layout.payload.payloadArena
  have pointerLower : inputPointer.toNat≤data.payload.toNat:=prepared.layout.payload.payloadLower
  have pointerBefore : data.payload.toNat+136≤root.toNat:=prepared.layout.payload.payloadBefore
  have number:=byteAddress_toNat data.payload cell.1 (by have h:=arena.upper; omega)
  change (data.payload+BitVec.ofNat 64 cell.1).toNat=data.payload.toNat+cell.1 at number
  have stored:=frame.cell origin source _ _ (data.payload+BitVec.ofNat 64 cell.1) cell.2
    (by rw [number]; exact Nat.le_trans pointerLower (Nat.le_add_right _ _))
    (by rw [number]; have h:=valid.1; omega) (prepared.image.payload.fields cell member)
  exact congrArg MemoryBytes.wordBits stored

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.input_word_of_image
