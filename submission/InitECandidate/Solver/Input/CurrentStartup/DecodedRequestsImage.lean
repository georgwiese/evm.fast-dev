import InitECandidate.Solver.Input.CurrentStartup.WitnessPrefixFrame
import InitECandidate.Solver.Input.Requests.DecodedImage

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
variable {decoderOrigin : DecoderOrigin} {input : Guest.InputBlob}
variable {source current post caller : PanSemStateFiniteExact 64 Guest.HostMemory}
variable {pointer statelessRecord record gasWord requestRecord : BitVec 64}
variable {payloadLength : Nat} {counts : Nat→BitVec 64} {value : ValueHOL 64}

theorem RequestCallerReturn.Result.requests_image
    (data : RequestCallerReturn.Result (decoderOrigin:=decoderOrigin) input caller current post pointer statelessRecord record gasWord requestRecord payloadLength counts value) :
    ∃ start size, Requests.DecodedImage input current pointer requestRecord start size counts := by
  obtain ⟨entry,bodyPost,start,size,decoded,endpoint⟩ := data.decoded
  have context := decoded.origin.context
  have inputArena : AllocatedBytes.Arena pointer (input.length%2^64) := ⟨by have h:=context.pointerLower; omega,by
    have a:=context.statelessLower; have b:=context.statelessRoom; omega⟩
  have inputBound : input.length%2^64≤251655056 := by
    have a:=context.pointerLower; have b:=context.statelessLower; have c:=context.recordAfter; have d:=data.requestAfter; have e:=data.requestRoom
    omega
  have arena : AllocatedBytes.Arena requestRecord 80 := ⟨by
    have a:=context.pointerLower; have b:=context.statelessLower; have c:=context.recordAfter; have d:=data.requestAfter; omega,by have h:=data.requestRoom; omega⟩
  have afterInput : pointer.toNat+input.length%2^64+8≤requestRecord.toNat := by
    have a:=context.statelessLower; have b:=context.recordAfter; have c:=data.requestAfter; omega
  refine ⟨start,size,?_,⟨decoded.first,decoded.valid⟩,decoded.origin.inside,decoded.origin.minimum,decoded.origin.startEq,decoded.origin.sizeEq,
    inputArena,inputBound,arena,data.requestAligned,data.requestRoom,context.pointerLower,afterInput⟩
  refine ⟨?_,decoded.arithmetic⟩
  intro index inside
  rw [endpoint]
  exact decoded.cells index inside

/-- Request fields lie after the stateless record and its six witness stores. -/
theorem request_field_ne_si
    (context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength)
    (afterRecord : record.toNat+136≤requestRecord.toNat) (room : requestRecord.toNat+80≤2952790016)
    (offset other : Nat) (inside : offset<80) (siInside : other≤88) :
    requestRecord+BitVec.ofNat 64 offset≠statelessRecord+BitVec.ofNat 64 other := by
  have number := byteAddress_toNat requestRecord offset (by omega)
  have siNumber := context.si_field_number input current pointer statelessRecord record gasWord payloadLength other siInside
  intro equal
  have same := congrArg BitVec.toNat equal
  change (byteAddress requestRecord offset).toNat=(statelessRecord+BitVec.ofNat 64 other).toNat at same
  rw [number,siNumber] at same
  have h:=context.recordAfter
  omega

theorem WitnessProtected.request_field
    (context : PayloadCallerReturn.Context input current pointer statelessRecord record gasWord payloadLength)
    (afterRecord : record.toNat+136≤requestRecord.toNat) (room : requestRecord.toNat+80≤2952790016)
    (offset : Nat) (inside : offset<80) : WitnessProtected statelessRecord record requestRecord (requestRecord+BitVec.ofNat 64 offset) := by
  have number := byteAddress_toNat requestRecord offset (by omega)
  refine ⟨?_,?_,?_⟩
  · change statelessRecord.toNat≤(byteAddress requestRecord offset).toNat
    rw [number]
    have h:=context.recordAfter
    omega
  · change (byteAddress requestRecord offset).toNat<max (record.toNat+136) (requestRecord.toNat+80)
    rw [number]
    omega
  · intro other member
    have bounded : other≤88 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> omega
    exact request_field_ne_si context afterRecord room offset other inside bounded

theorem WitnessEntry.Result.requests_image
    (data : WitnessEntry.Result (decoderOrigin:=decoderOrigin) input source current post pointer statelessRecord record gasWord requestRecord payloadLength value) :
    ∃ start size counts, Requests.DecodedImage input current pointer requestRecord start size counts := by
  obtain ⟨original,previous,previousPost,counts,decoded,originEq⟩ := data.origin
  obtain ⟨start,size,image⟩ := decoded.requests_image
  refine ⟨start,size,counts,image.of_memory ?_⟩
  intro index inside
  have kept (offset : Nat) (bound : offset<80) : current.memory (requestRecord+BitVec.ofNat 64 offset)=previous.memory (requestRecord+BitVec.ofNat 64 offset) := by
    rw [data.prepared]
    change source.memory (requestRecord+BitVec.ofNat 64 offset)=_
    rw [originEq]
    exact if_neg (request_field_ne_si decoded.context decoded.requestAfter decoded.requestRoom offset 32 bound (by decide))
  exact ⟨kept (16*index) (by omega),kept (16*index+8) (by omega)⟩

/-- All request fields, actual slice/layout/counts and physical input extent
survive the same witness execution to this exact main decoder snapshot. -/
theorem WitnessHeadersReturn.Snapshot.requests_image
    (snapshot : WitnessHeadersReturn.Snapshot (decoderOrigin:=decoderOrigin) input current pointer statelessRecord record gasWord requestRecord payloadLength) :
    ∃ start size counts, Requests.DecodedImage input current pointer requestRecord start size counts := by
  obtain ⟨original,prepared,originalPost,value,entry,memory⟩ := snapshot.prefix_frame
  obtain ⟨start,size,counts,image⟩ := entry.requests_image
  obtain ⟨caller,previous,previousPost,actualCounts,decoded,originEq⟩ := entry.origin
  refine ⟨start,size,counts,image.of_memory ?_⟩
  intro index inside
  exact ⟨memory _ (WitnessProtected.request_field entry.context decoded.requestAfter decoded.requestRoom (16*index) (by omega)),
    memory _ (WitnessProtected.request_field entry.context decoded.requestAfter decoded.requestRoom (16*index+8) (by omega))⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.RequestCallerReturn.Result.requests_image
#print axioms InitECandidate.Solver.Input.CurrentStartup.request_field_ne_si
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessProtected.request_field
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessEntry.Result.requests_image
#print axioms InitECandidate.Solver.Input.CurrentStartup.WitnessHeadersReturn.Snapshot.requests_image
