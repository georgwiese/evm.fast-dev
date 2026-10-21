import InitECandidate.Solver.Input.HashInputRegion
import InitECandidate.Solver.Input.HeapFrame
import InitECandidate.Solver.Input.PayloadImage
import InitECandidate.Solver.Input.VarList.RecordsIntervalFrame
import InitECandidate.Solver.WitnessRadix.MemoryAgreement

namespace InitECandidate.Solver.Input.HashInput
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Word agreement over the real aligned copied-input extent preserves its
exact byte relation; hash outputs and mutable workspaces may differ outside. -/
theorem Frame.heap_input (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64) (lower upper : Nat)
    (actual : Frame origin current lower upper) (bytes : Blob.HeapInput origin input pointer)
    (domain : current.memaddrs=origin.memaddrs) (endian : current.be=origin.be)
    (aligned : pointer.toNat%8=0) (fits : pointer.toNat+input.length%2^64<2^64)
    (after : lower≤pointer.toNat) (before : pointer.toNat+input.length%2^64≤upper) : Blob.HeapInput current input pointer := by
  intro offset inside
  have address : (pointer+BitVec.ofNat 64 offset).toNat=pointer.toNat+offset := byteAddress_toNat pointer offset (by omega)
  have query := AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 offset)
  rw [address] at query
  have word := actual.words (panByteAlignHOL (width:=64) (pointer+BitVec.ofNat 64 offset)) (by rw [query]; omega) (by rw [query]; omega)
  rw [MemoryBytes.read_of_cell current origin domain endian _ word]
  exact bytes offset inside

/-- Whole actual decoded payload metadata survives the same input frame,
including fields used by validation and gas initialization after hashing. -/
theorem Frame.payload_image (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer payload length array : BitVec 64) (lower upper : Nat)
    (actual : Frame origin current lower upper) (image : Payload.Image origin input pointer payload length array)
    (arena : AllocatedBytes.Arena payload 136) (after : lower≤payload.toNat) (before : payload.toNat+136≤upper) :
    Payload.Image current input pointer payload length array := by
  intro field member
  have valid := (Payload.image_fields_valid input pointer length array field member).1
  have number : (payload+BitVec.ofNat 64 field.1).toNat=payload.toNat+field.1 := byteAddress_toNat payload field.1 (by have h:=arena.upper; omega)
  exact (actual.words (payload+BitVec.ofNat 64 field.1) (by rw [number]; omega) (by rw [number]; omega)).trans (image field member)

/-- Actual decoded record evidence survives hashes whose writes are outside
its physical metadata interval, retaining original parsed offset validity. -/
theorem Frame.records (origin current : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array : BitVec 64) (start length lower upper : Nat)
    (actual : Frame origin current lower upper) (records : VarList.Records origin input pointer array start length)
    (after : lower≤array.toNat) (before : array.toNat+16*VarList.decodedCount input start length≤upper) :
    VarList.Records current input pointer array start length :=
  VarList.Records.of_interval origin current input pointer array start length upper records before
    (fun query low high=>actual.words query (Nat.le_trans after low) high)

end InitECandidate.Solver.Input.HashInput
#print axioms InitECandidate.Solver.Input.HashInput.Frame.heap_input
#print axioms InitECandidate.Solver.Input.HashInput.Frame.payload_image
#print axioms InitECandidate.Solver.Input.HashInput.Frame.records
