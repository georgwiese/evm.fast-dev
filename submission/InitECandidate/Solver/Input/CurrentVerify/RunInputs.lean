import InitECandidate.Solver.Input.CurrentHash.MainWitnessReturned
import InitECandidate.Solver.Input.CurrentHash.MainPayloadReturned
import InitECandidate.Solver.Input.CurrentVerify.PayloadImage
import InitECandidate.Solver.Input.CurrentVerify.CopiedInput
import InitECandidate.Solver.Input.VerifyTrace

namespace InitECandidate.Solver.Input.CurrentVerify
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def Witnesses (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si : BitVec 64) (boundary : Nat) : Prop :=
  ∃ nodes codes headers : BitVec 64,∃ nodeStart nodeLength codeStart codeLength headerStart headerLength : Nat,
    CurrentStartup.WitnessArrays.Image input source pointer si nodes nodeStart nodeLength boundary 40 1024 (2^31) ∧
    CurrentStartup.WitnessArrays.Image input source pointer si codes codeStart codeLength boundary 56 65536 (2^31) ∧
    CurrentStartup.WitnessArrays.Image input source pointer si headers headerStart headerLength boundary 72 1024 256

/-- The same actual decoded execution requests, including their SI
pointer, complete validated layout and original physical memory boundary. -/
def RequestImage (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si : BitVec 64) (boundary : Nat) : Prop:=
  ∃ rq start size counts,source.memory (si+32#64)=.word rq ∧ Requests.DecodedImage input source pointer rq start size counts ∧ rq.toNat+80≤boundary

/-- Physical inputs at the actual current verification/run_attempt entry.
No later header, database, scratch allocation or EVM success is assumed. -/
structure Data (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) : Prop where
  arena : CurrentStartup.ArenaState source
  little : source.be=false
  keccak : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64
  mptHash : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word 2701134768#64))
  mptKey : source.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word 2701134808#64))
  mptEmpty : source.globals.lookup (ofString "empty_trie_root")=some (.val (.word 2701134640#64))
  heap : NormalHeapEffects.AtLeast (boundary+32) source
  siLocal : source.locals.lookup (ofString "si")=some (.val (.word si))
  siArena : AllocatedBytes.Arena si 96
  siAligned : si.toNat%8=0
  recordArena : AllocatedBytes.Arena record 136
  recordAligned : record.toNat%8=0
  recordInside : 2701134824≤record.toNat ∧ record.toNat+136≤boundary
  payloadCell : source.memory si=.word record
  parentCell : source.memory (si+24#64)=.word (pointer+26#64)
  gasCell : source.memory (record+88#64)=.word gasWord
  gasBound : gasWord.toNat≤200000000
  payload : PayloadImage input source pointer record boundary
  copied : CopiedInput input source pointer record
  witnesses : Witnesses input source pointer si boundary
  requests : RequestImage input source pointer si boundary

/-- Shared transport of all decoded input facts through an actual earlier
memory interval. The advanced heap and hash/arena state are independently
obtained from the same normal caller; no later execution is assumed. -/
theorem Data.of_interval {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (arena : CurrentStartup.ArenaState target) (little : target.be=false)
    (environment : CurrentKeccak.Hash.Environment target 2701132160#64 2701132360#64)
    (mptHash : target.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word 2701134768#64)))
    (mptKey : target.globals.lookup (ofString "mpt_key_scratch")=some (.val (.word 2701134808#64)))
    (mptEmpty : target.globals.lookup (ofString "empty_trie_root")=some (.val (.word 2701134640#64)))
    (heap : NormalHeapEffects.AtLeast (boundary+32) target)
    (siLocal : target.locals.lookup (ofString "si")=some (.val (.word si)))
    (memory : ∀ query : BitVec 64,2701134824≤query.toNat→query.toNat<boundary→target.memory query=source.memory query) :
    Data input target pointer si record gasWord boundary := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  have siFrame (offset : Nat) (inside : offset<96) : target.memory (si+BitVec.ofNat 64 offset)=source.memory (si+BitVec.ofNat 64 offset) := by
    have number : (si+BitVec.ofNat 64 offset).toNat=si.toNat+offset:=byteAddress_toNat si offset (by have upper:=data.siArena.upper; omega)
    apply memory
    · rw [number]; have lower:=nodeImage.siLower; omega
    · rw [number]; have before:=nodeImage.siBefore; omega
  have siZero : target.memory si=source.memory si:=by simpa only [BitVec.add_zero] using siFrame 0 (by decide)
  have payloadCell : target.memory si=.word record:=siZero.trans data.payloadCell
  have gasNumber : (record+88#64).toNat=record.toNat+88:=byteAddress_toNat record 88 (by have upper:=data.recordArena.upper; omega)
  have gasFrame : target.memory (record+88#64)=source.memory (record+88#64):=memory _
    (by rw [gasNumber]; have lower:=data.recordInside.1; omega) (by rw [gasNumber]; have before:=data.recordInside.2; omega)
  obtain ⟨rq,requestStart,requestSize,counts,rqStored,requestImage,requestBefore⟩:=data.requests
  have requestMemory (offset : Nat) (inside : offset<80) : target.memory (rq+BitVec.ofNat 64 offset)=source.memory (rq+BitVec.ofNat 64 offset):=by
    have number:=byteAddress_toNat rq offset (by have upper:=requestImage.cursorArena.upper; omega)
    apply memory
    · change (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset at number
      have lower:=requestImage.inputLower
      have afterInput:=requestImage.cursorAfterInput
      omega
    · change (rq+BitVec.ofNat 64 offset).toNat=rq.toNat+offset at number
      omega
  have requests : RequestImage input target pointer si boundary:=⟨rq,requestStart,requestSize,counts,(siFrame 32 (by decide)).trans rqStored,
    requestImage.of_memory (by intro index inside; exact ⟨requestMemory (16*index) (by omega),requestMemory (16*index+8) (by omega)⟩),requestBefore⟩
  exact ⟨arena,little,environment,mptHash,mptKey,mptEmpty,heap,siLocal,data.siArena,data.siAligned,data.recordArena,data.recordAligned,data.recordInside,
    payloadCell,(siFrame 24 (by decide)).trans data.parentCell,gasFrame.trans data.gasCell,data.gasBound,
    data.payload.of_interval (fun query lower upper=>memory query (Nat.le_trans data.recordInside.1 lower) upper) heap,
    data.copied.of_interval boundary (by have before:=data.recordInside.2; omega) (arena.domain.trans data.arena.domain.symm) (little.trans data.little.symm) memory,
    ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) memory,codeImage.of_interval (by decide) memory,headerImage.of_interval (by decide) memory⟩,requests⟩

theorem Data.of_frame {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (frame : LocalEffects.erase post=LocalEffects.erase source)
    (siLocal : post.locals.lookup (ofString "si")=some (.val (.word si))) :
    Data input post pointer si record gasWord boundary := by
  have memory:=LocalEffects.memory_of_erase source post frame
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have code:=congrArg PanSemStateFiniteExact.code frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have endian:=congrArg PanSemStateFiniteExact.be frame
  change post.globals=source.globals at globals
  change post.code=source.code at code
  change post.memaddrs=source.memaddrs at domain
  change post.be=source.be at endian
  have nextArena : CurrentStartup.ArenaState post := ⟨by rw [globals]; exact data.arena.scratch,
    by rw [globals]; exact data.arena.frame,domain.trans data.arena.domain,by rw [code]; exact data.arena.code⟩
  obtain ⟨cursor,cell,lower,upper,aligned⟩ := data.heap
  have heap : NormalHeapEffects.AtLeast (boundary+32) post := ⟨cursor,by rw [globals]; exact cell,lower,upper,aligned⟩
  exact data.of_interval nextArena (endian.trans data.little) (data.keccak.of_frame frame)
    (by rw [globals]; exact data.mptHash) (by rw [globals]; exact data.mptKey) (by rw [globals]; exact data.mptEmpty) heap siLocal (by intro query lower upper; exact congrFun memory query)

/-- This contract is obtained from the same actual main decoder/root return. -/
theorem main_inputs {input : Guest.InputBlob} {decoded current post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {origin : CurrentStartup.DecoderOrigin} {record gasWord rq root array : BitVec 64} {length start size : Nat}
    (ready : CurrentHash.RootEntry.Ready input decoded current origin record gasWord rq root array length start size)
    (workspace : CurrentHash.WorkspaceEntry.Workspace current)
    (actual : evaluateHOLFiniteState current (.call (some (none,none)) (ofString "htr_new_payload_request") CurrentHash.RootEntry.arguments)=(none,post)) :
    Data input post origin.pointer origin.word record gasWord root.toNat := by
  obtain ⟨arena,next,heap,si⟩ := CurrentHash.RootHash.main_returned_state ready workspace actual
  obtain ⟨siArena,siAligned,recordArena,recordAligned,payloadCell,gasCell,gasBound⟩ := CurrentHash.RootHash.main_payload_cells ready workspace actual
  have recordInside : 2701134824≤record.toNat ∧ record.toNat+136≤root.toNat := by
    obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,data,frame,clock⟩:=ready.snapshot
    exact ⟨by have a:=data.context.pointerLower; have b:=data.context.statelessLower; have c:=data.context.recordAfter; omega,by have h:=ready.rootAfter; omega⟩
  have parentCell : post.memory (origin.word+24#64)=.word (origin.pointer+26#64):=by
    have parent:=ready.snapshot.request_fields.2.2.1
    obtain ⟨headerSource,headerReady,headerPost,nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,data,frame,clock⟩:=ready.snapshot
    have number : (origin.word+24#64).toNat=origin.word.toNat+24:=byteAddress_toNat origin.word 24 (by have upper:=data.context.statelessRoom; omega)
    have keptParent:=CurrentHash.RootHash.main_earlier_memory ready workspace actual (origin.word+24#64)
      (by rw [number]; have lower:=data.context.pointerLower; have before:=data.context.statelessLower; omega)
      (by rw [number]; have before:=data.context.recordAfter; have rootBefore:=ready.rootAfter; omega)
    simpa only [BitVec.add_assoc,show 18#64+8#64=26#64 from by decide] using keptParent.trans parent
  exact ⟨arena,next.little,next.keccak_environment,next.mptHash,next.mptKey,next.mptEmpty,heap,si,siArena,siAligned,recordArena,recordAligned,recordInside,payloadCell,parentCell,gasCell,gasBound,main_payload_image ready workspace actual,main_copied_input ready workspace actual,
    CurrentHash.RootHash.main_witness_images ready workspace actual,by
      obtain ⟨requestStart,requestSize,counts,cell,image,before⟩:=CurrentHash.RootHash.main_requests_image ready workspace actual
      exact ⟨rq,requestStart,requestSize,counts,cell,image,before⟩⟩

/-- The genuine eight-wrapper prefix carries these same physical inputs to
its actual run_attempt entry, or stops within eight source caller ticks. -/
theorem through_wrappers {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (result : Option (PanSemResultExact 64)) (actual : evaluateHOLFiniteState source Verify.body=(result,post)) :
    source.clock-post.clock≤8 ∨ ∃ entry target childResult,
      Data input entry pointer si record gasWord boundary ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
      entry.clock=source.clock-8 ∧ evaluateHOLFiniteState entry RunAttempt.body=(childResult,target) ∧ target.clock=post.clock := by
  rcases Verify.to_run source post si data.arena.code data.siLocal result actual with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨entry,target,childResult,siLocal,frame,clock,run,endpoint⟩ := reached
    exact Or.inr ⟨entry,target,childResult,data.of_frame frame siLocal,frame,clock,run,endpoint⟩

end InitECandidate.Solver.Input.CurrentVerify

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.of_frame
#print axioms InitECandidate.Solver.Input.CurrentVerify.main_inputs
#print axioms InitECandidate.Solver.Input.CurrentVerify.through_wrappers

#print axioms InitECandidate.Solver.Input.CurrentVerify.Data.of_interval
