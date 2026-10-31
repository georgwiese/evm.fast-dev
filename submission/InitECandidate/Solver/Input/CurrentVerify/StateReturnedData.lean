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
  have keyGlobal:=returned.globals (ofString "mpt_key_scratch") (by decide)
  have emptyGlobal:=returned.globals (ofString "empty_trie_root") (by decide)
  have shaStateGlobal:=returned.globals (ofString "sha_st") (by decide)
  have u256Global:=returned.globals (ofString "u256_ws") (by decide)
  have shaPadGlobal:=returned.globals (ofString "sha_pad") (by decide)
  obtain ⟨entry,value,inputs,entryFrame,bodyRun,checked⟩:=returned
  obtain ⟨heap,bs,heapCell,valueEq,records,priorMemory⟩:=state_init_normal_context inputs value bodyRun
  let current : PanSemStateFiniteExact 64 Guest.HostMemory:={target with locals:=caller.locals}
  have globals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change entry.globals=caller.globals at globals
  have callerHeap : caller.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)):=by rw [←globals]; exact heapCell
  obtain ⟨oldHeap,oldCell,oldLower,oldUpper,oldAligned⟩:=data.heap
  have heapEq : oldHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans callerHeap)))
  subst oldHeap
  obtain ⟨next,nextCell,nextArena,nextUpper,nextAligned,grows⟩:=records.heap
  have currentArena : CurrentStartup.ArenaState current:=records.arena.of_frame rfl
  have heapNow : NormalHeapEffects.AtLeast (boundary+32) current:=⟨next,nextCell,by omega,nextUpper,nextAligned⟩
  have fields:=evaluation_fields entry target Mpt.StateInit.body (some (.returned value)) bodyRun
  have entryEndian:=congrArg PanSemStateFiniteExact.be entryFrame
  change entry.be=caller.be at entryEndian
  have little : current.be=false:=fields.2.1.trans (entryEndian.trans data.little)
  have entryMemory:=LocalEffects.memory_of_erase caller entry entryFrame
  have environment : CurrentKeccak.Hash.Environment current 2701132160#64 2701132360#64:=
    ⟨currentArena.code,currentArena.domain,hashes.1.trans data.keccak.stateGlobal,hashes.2.1.trans data.keccak.padGlobal,
      data.keccak.stateArena,data.keccak.padArena,data.keccak.stateAligned,data.keccak.padAligned⟩
  exact data.of_interval currentArena little environment (hashes.2.2.trans data.mptHash) (keyGlobal.trans data.mptKey)
    (emptyGlobal.trans data.mptEmpty) (shaStateGlobal.trans data.shaState) (shaPadGlobal.trans data.shaPad) (u256Global.trans data.u256) heapNow data.siLocal
    (fun query low high=>(priorMemory query (by omega)).trans (congrFun entryMemory query))

/-- Main's actual complete state-init prefix now resumes with retained
physical inputs as well as the same original continued execution. -/
theorem to_after_state_init_with_data {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1760801932784 ∨ ∃ caller target inner,
      HasTables input caller pointer si record gasWord boundary ∧ StateInitReturned input caller target pointer si boundary ∧
      Data input {target with locals:=caller.locals} pointer si record gasWord boundary ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤1760801932784 ∧
      evaluateHOLFiniteState {target with locals:=caller.locals} afterStateInit=(outcome,inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rcases to_after_state_init data outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨caller,target,inner,tables,returned,forward,price,continued,endpoint,physical⟩:=reached
    exact Or.inr ⟨caller,target,inner,tables,returned,returned.data tables.1,forward,price,continued,endpoint,physical⟩

/-- Main's genuine normal state_init return supplies the actual typed and
owned workspace/block records, their ordering and the older-memory frame.
These are consequences of the same execution retained by the prefix trace. -/
theorem StateInitReturned.records {input : Guest.InputBlob} {caller target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si : BitVec 64} {boundary : Nat}
    (returned : StateInitReturned input caller target pointer si boundary) :
    ∃ ws bs,caller.globals.lookup (ofString "heap_ptr")=some (.val (.word ws)) ∧
      Mpt.StateInit.MemoryContext {target with locals:=caller.locals} ws ws bs ∧
      Mpt.WitnessCore.Stack.StablePrefix caller {target with locals:=caller.locals} ws.toNat := by
  obtain ⟨entry,value,inputs,entryFrame,bodyRun,checked⟩:=returned
  obtain ⟨ws,bs,heapCell,valueEq,physical,frame⟩:=state_init_normal_context inputs value bodyRun
  have globals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change entry.globals=caller.globals at globals
  have entryMemory:=LocalEffects.memory_of_erase caller entry entryFrame
  refine ⟨ws,bs,?_,physical.of_frame rfl,?_⟩
  · rw [←globals]
    exact heapCell
  · intro query earlier
    exact (frame query earlier).trans (congrFun entryMemory query)

/-- Retain those actual records at main's original post-state-init program
point, together with physical input, source price and the continued run. -/
theorem to_after_state_init_with_records {input : Guest.InputBlob} {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(outcome,post)) :
    source.clock-post.clock≤1760801932784 ∨ ∃ caller target inner ws bs,
      HasTables input caller pointer si record gasWord boundary ∧ StateInitReturned input caller target pointer si boundary ∧
      Data input {target with locals:=caller.locals} pointer si record gasWord boundary ∧
      caller.globals.lookup (ofString "heap_ptr")=some (.val (.word ws)) ∧
      Mpt.StateInit.MemoryContext {target with locals:=caller.locals} ws ws bs ∧
      Mpt.WitnessCore.Stack.StablePrefix caller {target with locals:=caller.locals} ws.toNat ∧
      target.clock≤source.clock ∧ source.clock-target.clock≤1760801932784 ∧
      evaluateHOLFiniteState {target with locals:=caller.locals} afterStateInit=(outcome,inner) ∧
      post.clock=inner.clock ∧ LocalEffects.erase post=LocalEffects.erase inner := by
  rcases to_after_state_init_with_data data outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨caller,target,inner,tables,returned,physical,forward,price,continued,clock,scope⟩:=reached
    obtain ⟨ws,bs,cell,records,frame⟩:=returned.records
    exact Or.inr ⟨caller,target,inner,ws,bs,tables,returned,physical,cell,records,frame,forward,price,continued,clock,scope⟩

end InitECandidate.Solver.Input.CurrentVerify.RunAttempt

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.data
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_state_init_with_data

#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.StateInitReturned.records
#print axioms InitECandidate.Solver.Input.CurrentVerify.RunAttempt.to_after_state_init_with_records
