import InitECandidate.Solver.Input.CurrentHash.MainWitnessReturned
import InitECandidate.Solver.Input.CurrentHash.MainPayloadReturned
import InitECandidate.Solver.Input.CurrentVerify.PayloadImage
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

/-- Physical inputs at the actual current verification/run_attempt entry.
No later header, database, scratch allocation or EVM success is assumed. -/
structure Data (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer si record gasWord : BitVec 64) (boundary : Nat) : Prop where
  arena : CurrentStartup.ArenaState source
  little : source.be=false
  keccak : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64
  mptHash : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word 2701134768#64))
  heap : NormalHeapEffects.AtLeast (boundary+32) source
  siLocal : source.locals.lookup (ofString "si")=some (.val (.word si))
  siArena : AllocatedBytes.Arena si 96
  siAligned : si.toNat%8=0
  recordArena : AllocatedBytes.Arena record 136
  recordAligned : record.toNat%8=0
  recordInside : 2701134824≤record.toNat ∧ record.toNat+136≤boundary
  payloadCell : source.memory si=.word record
  gasCell : source.memory (record+88#64)=.word gasWord
  gasBound : gasWord.toNat≤200000000
  payload : PayloadImage input source pointer record boundary
  witnesses : Witnesses input source pointer si boundary

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
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩ := data.witnesses
  have interval (query : BitVec 64) (_lower : 2701134824≤query.toNat) (_upper : query.toNat<boundary) : post.memory query=source.memory query := congrFun memory query
  exact ⟨nextArena,endian.trans data.little,data.keccak.of_frame frame,(by rw [globals]; exact data.mptHash),heap,siLocal,data.siArena,data.siAligned,data.recordArena,data.recordAligned,data.recordInside,
    (congrFun memory _).trans data.payloadCell,(congrFun memory _).trans data.gasCell,data.gasBound,data.payload.of_frame frame,
    nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) interval,codeImage.of_interval (by decide) interval,headerImage.of_interval (by decide) interval⟩

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
  exact ⟨arena,next.little,next.keccak_environment,next.mptHash,heap,si,siArena,siAligned,recordArena,recordAligned,recordInside,payloadCell,gasCell,gasBound,main_payload_image ready workspace actual,
    CurrentHash.RootHash.main_witness_images ready workspace actual⟩

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
