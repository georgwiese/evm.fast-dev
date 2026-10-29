import InitECandidate.Solver.Input.CurrentHash.RootState
import InitECandidate.Solver.Input.CurrentHash.InvocationFrame
import InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.RootHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- The actual128-byte parent allocation preserves the same decoder images
and supplies its own mapped chunk extent, bound/alignment and next frontier.
Its room and nonlocal post-state are obtained from that same real return. -/
theorem allocated {input : Guest.InputBlob} {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {blob si record rq root array cursor : BitVec 64} {length start size : Nat}
    (data : Invocation.Data input source blob si record rq root array length start size)
    (rootBefore : root.toNat+32≤cursor.toNat) (bounded : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (room : cursor.toNat+128≤2952790016) (same : LocalEffects.erase target=LocalEffects.erase (PersistentAlloc.post source cursor 128#64)) :
    State input (CallNormal.continuationEntry source target "ch" (.val (.word cursor))) blob si record rq root array cursor (PersistentAlloc.rounded cursor 128#64) length start size := by
  let entry := CallNormal.continuationEntry source target "ch" (.val (.word cursor))
  have codeFrame := congrArg PanSemStateFiniteExact.code same
  have code : entry.code=source.code := codeFrame
  have domainFrame := congrArg PanSemStateFiniteExact.memaddrs same
  have domain : entry.memaddrs=source.memaddrs := domainFrame
  have endianFrame := congrArg PanSemStateFiniteExact.be same
  have endian : entry.be=source.be := endianFrame
  have memory : entry.memory=source.memory := LocalEffects.memory_of_erase (PersistentAlloc.post source cursor 128#64) target same
  have globals := congrArg PanSemStateFiniteExact.globals same
  change entry.globals=(source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor 128#64)))) at globals
  have cell (name : String) (different : ofString "heap_ptr"≠ofString name) : entry.globals.lookup (ofString name)=source.globals.lookup (ofString name) := by
    rw [globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,different]
  have installed : OriginalCode.Installed entry.code := by rw [code]; exact data.workspace.code
  have workspace : WorkspaceEntry.Workspace entry := ⟨installed,domain.trans data.workspace.domain,endian.trans data.workspace.little,
    (cell "ssz_offs" (by decide)).trans data.workspace.offsets,(cell "ssz_len_chunk" (by decide)).trans data.workspace.chunk,(cell "zero_hashes" (by decide)).trans data.workspace.zeros,
    (cell "keccak_st" (by decide)).trans data.workspace.keccakState,(cell "keccak_pad" (by decide)).trans data.workspace.keccakPad,(cell "mpt_hash_scratch" (by decide)).trans data.workspace.mptHash,(cell "mpt_key_scratch" (by decide)).trans data.workspace.mptKey,
    data.workspace.chunkArena,data.workspace.zeroArena,data.workspace.chunkAligned,data.workspace.zeroAligned⟩
  have arena : CurrentStartup.ArenaState entry := ⟨(cell "scratch_ptr" (by decide)).trans data.arena.scratch,(cell "frame_mem_ptr" (by decide)).trans data.arena.frame,workspace.domain,installed⟩
  have heap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor 128#64))) := by
    rw [globals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have guards := PersistentAlloc.guards cursor 128#64 room
  have nextHeap : NormalHeapEffects.AtLeast (root.toNat+32) entry :=
    ⟨_,heap,by have h:=guards.2.2.1; omega,guards.2.2.2.1,guards.2.2.2.2⟩
  have kept (name : String) (different : ofString "ch"≠ofString name) := CallNormal.continuation_lookup_other source target "ch" name (.val (.word cursor)) different
  have next := data.of_interval workspace arena nextHeap ((kept "si" (by decide)).trans data.si) ((kept "out" (by decide)).trans data.out) cursor.toNat rootBefore
    (by intro query lower upper; exact congrFun memory query)
  have lower : 2701131776≤cursor.toNat := by have h:=data.rootArena.lower; omega
  exact ⟨next,CallNormal.continuation_lookup_same source target "ch" (.val (.word cursor)),⟨lower,by omega⟩,aligned,rootBefore,heap,guards.2.2.2.1,guards.2.2.2.2,guards.2.2.1⟩

end InitECandidate.Solver.Input.CurrentHash.RootHash

#print axioms InitECandidate.Solver.Input.CurrentHash.RootHash.allocated
