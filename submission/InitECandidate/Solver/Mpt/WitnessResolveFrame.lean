import InitECandidate.Solver.Mpt.WitnessResolveHashNormal
import InitECandidate.Solver.Mpt.NodeConstructorCells
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.WitnessResolve
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem hash_allocated_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64)
    (arena : AllocatedBytes.Arena heap 32) (aligned : heap.toNat%8=0) :
    ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+32≤query.toNat→(hashAllocated source heap hash).memory query=source.memory query := by
  let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,32⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨arena.lower,arena.upper,aligned⟩
  intro query outside
  have away:=FieldStores.writes_outside source.memory region valid (NodeConstructor.fields .hashed (hashWords hash))
    (fun field inside=>(NodeConstructor.fields_geometry .hashed (hashWords hash) field inside).1) query outside
  simpa only [hashAllocated,region,MutableTable.MemoryRegion.pointer,BitVec.ofNat_toNat,BitVec.setWidth_eq] using away

theorem hash_allocated_tag (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64) :
    (hashAllocated source heap hash).memory heap=.word 0#64 := by
  have tag:=WordWrites.write_unique source.memory (FieldStores.writes heap (NodeConstructor.fields .hashed (hashWords hash))) (heap+0#64,0#64)
    (NodeConstructor.fields_distinct .hashed (hashWords hash) heap) (by simp [FieldStores.writes,NodeConstructor.fields,FieldStores.Value.word])
  simpa only [hashAllocated,BitVec.add_zero] using tag

theorem hash_allocated_hash (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64) :
    (hashAllocated source heap hash).memory (heap+24#64)=.word hash := by
  have cell:=WordWrites.write_unique source.memory (FieldStores.writes heap (NodeConstructor.fields .hashed (hashWords hash))) (heap+24#64,hash)
    (NodeConstructor.fields_distinct .hashed (hashWords hash) heap) (by simp [FieldStores.writes,NodeConstructor.fields,FieldStores.Value.word,hashWords])
  simpa only [hashAllocated] using cell

theorem hash_allocated_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) : Rlp.Validation.Arena (hashAllocated source heap hash) cursor limit := by
  refine ⟨arena.domain,?_,?_,arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  · simpa [hashAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "scratch_ptr" from by decide] using arena.cursorGlobal
  · simpa [hashAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "heap_ptr"≠ofString "frame_mem_ptr" from by decide] using arena.limitGlobal

theorem hash_allocated_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64)
    (arena : AllocatedBytes.Arena heap 32) :
    let next:=PersistentAlloc.rounded heap 32#64
    (hashAllocated source heap hash).globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
      AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat+32≤next.toNat := by
  have checked:=PersistentAlloc.guards heap 32#64 arena.upper
  refine ⟨?_,⟨?_,?_⟩,checked.2.2.2.2,checked.2.2.1⟩
  · simp [hashAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · have lower:=arena.lower; have grows:=checked.2.2.1; omega
  · have upper:=checked.2.2.2.1; omega

theorem hash_allocated_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap hash : BitVec 64)
    (key : MlS) (other : key≠ofString "heap_ptr") :
    (hashAllocated source heap hash).globals.lookup key=source.globals.lookup key := by
  simp [hashAllocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

end InitECandidate.Solver.Mpt.WitnessResolve

#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_memory
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_tag
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_hash
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_arena
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_heap
#print axioms InitECandidate.Solver.Mpt.WitnessResolve.hash_allocated_global
