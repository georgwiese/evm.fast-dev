import InitECandidate.Solver.Input.CurrentVerify.StateInitMemory
import InitECandidate.Solver.Input.CurrentVerify.StateGlobalFrame

namespace InitECandidate.Solver.Input.CurrentVerify.RunAttempt
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual normal state-init return retains main's real input/SI,
gas word, witness arrays and hash workspaces at its saved-caller continuation.
The genuinely advanced heap comes from that same callee execution. -/
theorem StateInitReturned.data {input : Guest.InputBlob} {caller target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (returned : StateInitReturned input caller target pointer si boundary)
    (data : Data input caller pointer si record gasWord boundary) :
    Data input {target with locals:=caller.locals} pointer si record gasWord boundary := by
  have hashes:=returned.hash_globals
  obtain ⟨entry,value,inputs,entryFrame,bodyRun,checked⟩:=returned
  obtain ⟨heap,heapCell,valueEq,targetArena,physical⟩:=state_init_normal_memory inputs value bodyRun
  let current : PanSemStateFiniteExact 64 Guest.HostMemory:={target with locals:=caller.locals}
  have frame : PersistentMemoryFrame caller current heap:=physical.of_erase entry target caller current heap entryFrame.symm rfl
  have globals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change entry.globals=caller.globals at globals
  have callerHeap : caller.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [←globals]; exact heapCell
  obtain ⟨oldHeap,oldCell,oldLower,oldUpper,oldAligned⟩:=data.heap
  have heapEq : oldHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans callerHeap)))
  subst oldHeap
  obtain ⟨next,nextCell,nextArena,nextUpper,nextAligned,grows⟩:=frame.nextHeap
  have currentArena : CurrentStartup.ArenaState current:=targetArena.of_frame rfl
  have heapNow : NormalHeapEffects.AtLeast (boundary+32) current:=⟨next,nextCell,by omega,nextUpper,nextAligned⟩
  have little : current.be=false:=(MemoryMetadata.endian frame.metadata).trans data.little
  have environment : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64:=
    ⟨currentArena.code,currentArena.domain,hashes.1.trans data.keccak.stateGlobal,hashes.2.1.trans data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  have interval (query : BitVec 64) (_lower : 2701134824≤query.toNat) (upper : query.toNat<boundary) : current.memory query=caller.memory query:=frame.memory query (by omega)
  have siFrame : current.memory si=caller.memory si:=frame.memory si (by have before:=nodeImage.siBefore; omega)
  have gasNumber : (record+88#64).toNat=record.toNat+88:=byteAddress_toNat record 88 (by have upper:=data.recordArena.upper; omega)
  have gasFrame : current.memory (record+88#64)=caller.memory (record+88#64):=frame.memory _ (by rw [gasNumber]; have before:=data.recordInside.2; omega)
  exact ⟨currentArena,little,environment,hashes.2.2.trans data.mptHash,heapNow,data.siLocal,data.siArena,data.siAligned,
    data.recordArena,data.recordAligned,data.recordInside,siFrame.trans data.payloadCell,gasFrame.trans data.gasCell,data.gasBound,
    data.payload.of_interval (fun query lower upper=>frame.memory query (by omega)) heapNow,
    nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,
    nodeImage.of_interval (by decide) interval,codeImage.of_interval (by decide) interval,headerImage.of_interval (by decide) interval⟩

/-- Main's actual complete state-init prefix now resumes with retained
physical inputs as well as the same original continued execution. -/
theorem to_after_state_init_with_data {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤3374969779 ∨ ∃ caller target inner,
      HasTables input caller pointer si record gasWord boundary ∧ StateInitReturned input caller target pointer si boundary ∧
      Data input {target with locals:=caller.locals} pointer si record gasWord boundary ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤3374969779 ∧
      evaluateHOLFiniteState {target with locals:=caller.locals} afterStateInit=(outcome,inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rcases to_after_state_init data outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨caller,target,inner,tables,returned,forward,price,continued,endpoint,physical⟩:=reached
    exact Or.inr ⟨caller,target,inner,tables,returned,returned.data tables.1,forward,price,continued,endpoint,physical⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.data
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_state_init_with_data
