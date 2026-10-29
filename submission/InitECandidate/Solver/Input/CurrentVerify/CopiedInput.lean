import InitECandidate.Solver.Input.CurrentHash.MainPayloadReturned
import InitECandidate.Solver.Input.InputImageFrame
import InitECandidate.Solver.Input.MemoryMetadata

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix

/-- Exact copied bytes over the encoded extent and their actual aligned
input allocation before the decoded payload record. -/
structure CopiedInput (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record : BitVec 64) : Prop where
  bytes : Blob.HeapInput source input pointer
  lower : 2701134824≤pointer.toNat
  aligned : pointer.toNat%8=0
  beforeRecord : pointer.toNat+input.length%2^64+8≤record.toNat

theorem CopiedInput.of_frame {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} (data : CopiedInput input source pointer record)
    (frame : LocalEffects.erase target=LocalEffects.erase source) : CopiedInput input target pointer record := by
  have memory:=LocalEffects.memory_of_erase source target frame
  have metadata:=MemoryMetadata.of_frame frame
  exact ⟨Blob.HeapInput.of_fields source target input pointer memory.symm (MemoryMetadata.domain metadata).symm (MemoryMetadata.endian metadata).symm data.bytes,
    data.lower,data.aligned,data.beforeRecord⟩

theorem CopiedInput.of_interval_from {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} (data : CopiedInput input source pointer record) (cutoff : Nat) (inputLower : cutoff≤pointer.toNat) (boundary : Nat)
    (recordBefore : record.toNat≤boundary) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,cutoff≤query.toNat→query.toNat<boundary→target.memory query=source.memory query) :
    CopiedInput input target pointer record := by
  refine ⟨Blob.HeapInput.of_words source target input pointer data.bytes domain endian ?_,data.lower,data.aligned,data.beforeRecord⟩
  intro offset inside
  have number:=MemoryBytes.offset_toNat pointer offset (by have before:=data.beforeRecord; have upper:=record.isLt; omega)
  have backing:=AllocatedBytes.aligned_number (pointer+BitVec.ofNat 64 offset)
  apply memory
  · rw [backing,number]
    have lower:=inputLower
    have aligned:=data.aligned
    omega
  · rw [backing,number]
    have before:=data.beforeRecord
    omega


theorem CopiedInput.of_interval {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer record : BitVec 64} (data : CopiedInput input source pointer record) (boundary : Nat)
    (recordBefore : record.toNat≤boundary) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<boundary→target.memory query=source.memory query) :
    CopiedInput input target pointer record := by
  exact data.of_interval_from 2701134824 data.lower boundary recordBefore domain endian memory

/-- The same real final decoder snapshot supplies the original byte image;
main's actual root-hash call retains every physical backing word of it. -/
theorem main_copied_input {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : CurrentHash.RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : CurrentHash.WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (Flapjack.Basis.Pure.MlString.ofString "htr_new_payload_request") CurrentHash.RootEntry.arguments)=(none,post)) :
    CopiedInput input post origin.pointer record := by
  obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,data,frame,clock⟩:=ready.snapshot
  have decodedMemory:=LocalEffects.memory_of_erase headerPost decoded frame
  have decodedMetadata:=MemoryMetadata.of_frame frame
  have oldMetadata:=MemoryMetadata.of_frame data.frame
  have copied : CopiedInput input decoded origin.pointer record:=
    ⟨Blob.HeapInput.of_fields headerPost decoded input origin.pointer decodedMemory.symm (MemoryMetadata.domain decodedMetadata).symm
      (MemoryMetadata.endian decodedMetadata).symm data.image,data.context.pointerLower,data.context.pointerAligned,
      by have before:=data.context.statelessLower; have afterRecord:=data.context.recordAfter; omega⟩
  have decodedDomain : decoded.memaddrs=InitE.ordinaryDomain:=
    (MemoryMetadata.domain decodedMetadata).trans ((MemoryMetadata.domain oldMetadata).trans data.context.domain)
  have decodedEndian : decoded.be=false:=
    (MemoryMetadata.endian decodedMetadata).trans ((MemoryMetadata.endian oldMetadata).trans data.context.endian)
  obtain ⟨postArena,postWorkspace,heap,si⟩:=CurrentHash.RootHash.main_returned_state ready workspace actual
  apply copied.of_interval root.toNat
  · have before:=ready.rootAfter
    omega
  · exact postArena.domain.trans decodedDomain.symm
  · exact postWorkspace.little.trans decodedEndian.symm
  · exact CurrentHash.RootHash.main_earlier_memory ready workspace actual

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.CopiedInput.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.CopiedInput.of_interval
#print axioms InitECandidate.Solver.Input.CurrentVerify.main_copied_input

#print axioms InitECandidate.Solver.Input.CurrentVerify.CopiedInput.of_interval_from
