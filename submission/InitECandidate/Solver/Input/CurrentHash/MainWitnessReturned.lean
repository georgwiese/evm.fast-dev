import InitECandidate.Solver.Input.CurrentHash.RootReturned
import InitECandidate.Solver.Input.CurrentStartup.DecodedWitnessImages
import InitECandidate.Solver.Input.CurrentStartup.DecodedRequestsImage

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Main's actual normal root return carries all three original witness
arrays and six physical SI fields into stateless verification. Every image
comes from the same decoder, through the actual root allocation and hash call. -/
theorem main_witness_images {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    ∃ nodes codes headers : BitVec 64,∃ nodeStart nodeLength codeStart codeLength headerStart headerLength : Nat,
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word nodes nodeStart nodeLength root.toNat 40 1024 (2^31) ∧
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word codes codeStart codeLength root.toNat 56 65536 (2^31) ∧
      CurrentStartup.WitnessArrays.Image input post origin.pointer origin.word headers headerStart headerLength root.toNat 72 1024 256 := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩ :=
    ready.snapshot.witness_images ready.enteringHeap
  have memory := main_earlier_memory ready workspace actual
  exact ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) memory,codeImage.of_interval (by decide) memory,headerImage.of_interval (by decide) memory⟩

/-- The same actual decoder/root return retains the request-record
pointer and complete decoded five-list image before the original boundary.
No later execution-request encoder or hash result is assumed. -/
theorem main_requests_image {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") RootEntry.arguments)=(none,post)) :
    ∃ requestStart requestSize counts,post.memory (origin.word+32#64)=.word rq ∧ Requests.DecodedImage input post origin.pointer rq requestStart requestSize counts ∧ rq.toNat+80≤root.toNat := by
  obtain ⟨requestStart,requestSize,counts,image⟩:=ready.snapshot.requests_image
  have rqBefore : rq.toNat+80≤root.toNat:=by have afterRoot:=ready.rootAfter; omega
  have fields (offset : Nat) (inside : offset<80) : post.memory (rq+BitVec.ofNat 64 offset)=decoded.memory (rq+BitVec.ofNat 64 offset):=by
    have number:=byteAddress_toNat rq offset (by have upper:=image.cursorArena.upper; omega)
    apply main_earlier_memory ready workspace actual
    · change (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset at number
      have lower:=image.inputLower
      have afterInput:=image.cursorAfterInput
      omega
    · change (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset at number
      omega
  have pointerStored:=ready.snapshot.request_fields.2.2.2
  have pointerFrame : post.memory (origin.word+32#64)=decoded.memory (origin.word+32#64):=by
    obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,data,frame,clock⟩:=ready.snapshot
    have number : (origin.word+32#64).toNat=origin.word.toNat+32:=byteAddress_toNat origin.word 32 (by have upper:=data.context.statelessRoom; omega)
    exact main_earlier_memory ready workspace actual _
      (by rw [number]; have lower:=data.context.pointerLower; have before:=data.context.statelessLower; omega)
      (by rw [number]; have before:=data.context.recordAfter; have afterRoot:=ready.rootAfter; omega)
  exact ⟨requestStart,requestSize,counts,pointerFrame.trans pointerStored,image.of_memory (by
    intro index inside
    exact ⟨fields (16*index) (by omega),fields (16*index+8) (by omega)⟩),rqBefore⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_witness_images

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.main_requests_image
