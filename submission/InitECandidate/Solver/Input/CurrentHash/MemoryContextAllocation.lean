import InitECandidate.Solver.Input.CurrentHash.MerkleMemory
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def entry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor amount : BitVec 64) (name : String) :=
  bind (PersistentAlloc.post {source with clock:=source.clock-1} cursor amount) name cursor

theorem context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor amount zeros query : BitVec 64) (name : String)
    (data : MerkleMemory.Context source cursor zeros query) (room : cursor.toNat+amount.toNat≤2952790016) :
    MerkleMemory.Context (entry source cursor amount name) (PersistentAlloc.rounded cursor amount) zeros query := by
  have guards := PersistentAlloc.guards cursor amount room
  have heap : (entry source cursor amount name).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor amount))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor amount)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have zero : (entry source cursor amount name).globals.lookup (ofString "zero_hashes")=some (.val (.word zeros)) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded cursor amount)))).lookup (ofString "zero_hashes")=_
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,show ofString "heap_ptr"≠ofString "zero_hashes" from by decide] using data.zeroCell
  exact ⟨data.installed,data.domain,zero,data.zeroArena,heap,by have h:=data.heapLower; have g:=guards.2.2.1; omega,
    guards.2.2.2.1,guards.2.2.2.2,by have h:=data.below; have g:=guards.2.2.1; omega⟩

/-- Share normal actual allocation inversion: the returning allocator derives
its real room, physical arena and next context before the same continuation. -/
theorem scope_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor amount zeros query : BitVec 64)
    (data : MerkleMemory.Context source cursor zeros query) (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (PersistentAlloc.values amount))
    (tail : ∀ inner, MerkleMemory.Context (entry source cursor amount name) (PersistentAlloc.rounded cursor amount) zeros query →
      AllocatedBytes.Arena cursor amount.toNat → ∀ value,
      evaluateHOLFiniteState (entry source cursor amount name) continuation=(some (.returned value),inner) → inner.memory query=source.memory query)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source (.decCall (ofString name) .one (ofString "alloc") arguments continuation)=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  obtain ⟨room,positive,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post name arguments continuation cursor amount args
    (PersistentAlloc.original_code source.code data.installed) (Trap.original_code source.code data.installed) data.heap data.heapBound value actual
  have arena : AllocatedBytes.Arena cursor amount.toNat := ⟨data.heapLower,by omega⟩
  have frame := tail inner (context source cursor amount zeros query name data room) arena value remaining
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation

#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation.context
#print axioms InitECandidate.Solver.Input.CurrentHash.MemoryContextAllocation.scope_memory
