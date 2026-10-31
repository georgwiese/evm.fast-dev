import InitECandidate.Solver.Mpt.CompactToNibblesCurrentSnapshot
import InitECandidate.Solver.Input.PersistentNormalFrame
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Input Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Retain the complete runtime, nonheap globals and all earlier words
from the actual compact conversion snapshot. -/
theorem CurrentSnapshot.persistent_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {length nibbles : Nat} {heap leaf : BitVec 64}
    (snapshot : CurrentSnapshot source target length heap nibbles leaf) : PersistentNormalFrame source target heap := by
  have globals:=congrArg PanSemStateFiniteExact.globals snapshot.metadata
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (2*length))).globals at globals
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase {state with globals:=source.globals}) snapshot.metadata
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source at metadata
  exact ⟨⟨_,snapshot.heapCell,snapshot.nextArena,snapshot.nextBound,snapshot.nextAligned,by have grows:=snapshot.grows; omega⟩,metadata,
    by intro key other; rw [globals]; simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other],
    fun query before=>snapshot.memory query (Or.inl before)⟩

/-- Restore caller locals while retaining the actual compact post-state. -/
theorem CurrentSnapshot.resumed {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {length nibbles : Nat} {heap leaf : BitVec 64}
    (snapshot : CurrentSnapshot source target length heap nibbles leaf) (name : String) :
    CurrentSnapshot source (CallNormal.continuationEntry source target name (output heap nibbles leaf)) length heap nibbles leaf :=
  ⟨snapshot.positive,snapshot.outputArena,snapshot.nibbleBound,snapshot.leafBinary,snapshot.arena.of_frame rfl,
    snapshot.heapCell,snapshot.nextArena,snapshot.nextBound,snapshot.nextAligned,snapshot.grows,snapshot.metadata,snapshot.memory⟩

/-- Compact allocation retains the actual named scratch cursor and limit. -/
theorem CurrentSnapshot.scratch {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {length nibbles : Nat} {heap leaf cursor limit : BitVec 64}
    (snapshot : CurrentSnapshot source target length heap nibbles leaf)
    (arena : Rlp.Validation.Arena source cursor limit) : Rlp.Validation.Arena target cursor limit := by
  have persistent:=snapshot.persistent_frame
  have domain:=MemoryMetadata.domain persistent.metadata
  change target.memaddrs=source.memaddrs at domain
  exact ⟨domain.trans arena.domain,
    (persistent.globals (ofString "scratch_ptr") (by decide)).trans arena.cursorGlobal,
    (persistent.globals (ofString "frame_mem_ptr") (by decide)).trans arena.limitGlobal,
    arena.ordered,arena.aligned,arena.lower,arena.upper⟩

/-- The genuine compact buffer stays below the persistent cap, while all
older scratch records start at or above the entering cursor. -/
theorem CurrentSnapshot.live_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    {length nibbles : Nat} {heap leaf cursor limit : BitVec 64}
    (snapshot : CurrentSnapshot source target length heap nibbles leaf)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) :
    WitnessDecode.LiveFrame source target heap cursor limit := by
  have bounds:=live.bounds arena
  exact WitnessDecode.LiveFrame.of_persistent source target heap cursor limit live arena snapshot.persistent_frame
    (fun query above=>snapshot.memory query (Or.inr (by have grows:=snapshot.grows; have bound:=snapshot.nextBound; have ordered:=arena.ordered; omega)))

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.CurrentSnapshot.persistent_frame
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.CurrentSnapshot.resumed
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.CurrentSnapshot.scratch
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.CurrentSnapshot.live_frame
