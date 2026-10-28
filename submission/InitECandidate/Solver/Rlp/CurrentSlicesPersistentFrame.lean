import InitECandidate.Solver.Rlp.CurrentSlicesMemory
import InitECandidate.Solver.Input.PersistentNormalFrame

namespace InitECandidate.Solver.Rlp.CurrentSlices
open Slices Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Package the actual converter's normal-return allocation, runtime and
fresh-array window into the shared persistent frame. -/
theorem persistent_frame_of_return (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap count : BitVec 64) (heapArena : AllocatedBytes.Arena heap 0)
    (room : heap.toNat+16*count.toNat≤2952790016)
    (metadata : MemoryMetadata.erase target=MemoryMetadata.erase (PersistentAlloc.post source heap (count*16#64)))
    (window : Window source target heap.toNat (heap.toNat+16*count.toNat)) : PersistentNormalFrame source target heap := by
  have product : (count*16#64).toNat=16*count.toNat := by
    rw [BitVec.toNat_mul,Nat.mod_eq_of_lt (by change count.toNat*16<2^64; omega)]
    change count.toNat*16=16*count.toNat
    omega
  have checked:=PersistentAlloc.guards heap (count*16#64) (by rw [product]; exact room)
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=(PersistentAlloc.post source heap (count*16#64)).globals at globals
  have nextCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (count*16#64)))) := by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (count*16#64)) 0:=
    ⟨by have lower:=heapArena.lower; have grows:=checked.2.2.1; omega,by have upper:=checked.2.2.2.1; omega⟩
  have runtime:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase {state with globals:=source.globals}) metadata
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source at runtime
  exact ⟨⟨_,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,by have grows:=checked.2.2.1; omega⟩,runtime,
    by intro key other; rw [globals]; simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other],
    fun query before=>window query (Or.inl before)⟩

theorem body_persistent_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : CurrentStartup.ArenaState source)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016)
    (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    PersistentNormalFrame source target heap := by
  obtain ⟨items,count,model,countEq,countBound,valueEq,records,room,nextArena,globals,window,metadata,price⟩:=
    body_normal source target pointer length heap pointerCell lengthCell arena heapCell heapBound before sizeBound value normal
  exact persistent_frame_of_return source target heap count heapArena room metadata window

end InitECandidate.Solver.Rlp.CurrentSlices

#print axioms InitECandidate.Solver.Rlp.CurrentSlices.persistent_frame_of_return
#print axioms InitECandidate.Solver.Rlp.CurrentSlices.body_persistent_frame
