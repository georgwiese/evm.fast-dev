import InitECandidate.Solver.Mpt.StateInitPrefixTrace
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The workspace's real stores protect every earlier database/input word. -/
theorem ready_memory_before (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes query : BitVec 64) (room : heap.toNat+40≤2952790016)
    (before : query.toNat<heap.toNat) :
    (ready source heap nodes root codes).memory query=source.memory query := by
  have different (offset : Nat) (small : offset<40) : query≠heap+BitVec.ofNat 64 offset := by
    have number := byteAddress_toNat heap offset (by omega)
    intro equal
    have observed:=congrArg BitVec.toNat equal
    change query.toNat=(byteAddress heap offset).toNat at observed
    rw [number] at observed
    omega
  simp only [ready,written,allocated,putGlobal,PersistentAlloc.post,StoreWord.put,
    if_neg (different 0 (by decide)),if_neg (different 8 (by decide)),if_neg (different 16 (by decide))]

/-- Scratch/frame/code/domain facts survive the actual persistent allocation
and ws binding, rather than requiring a future initializer return. -/
theorem ready_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nodes root codes : BitVec 64) (arena : CurrentStartup.ArenaState source) :
    CurrentStartup.ArenaState (ready source heap nodes root codes) := by
  refine ⟨?_,?_,arena.domain,arena.code⟩
  · simpa [ready,written,allocated,putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide,
      show ofString "ws"≠ofString "scratch_ptr" from by decide] using arena.scratch
  · simpa [ready,written,allocated,putGlobal,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide,
      show ofString "ws"≠ofString "frame_mem_ptr" from by decide] using arena.frame

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.ready_memory_before
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_arena
