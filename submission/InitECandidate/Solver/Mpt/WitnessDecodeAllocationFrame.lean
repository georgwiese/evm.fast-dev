import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Mpt.WitnessDecodeMemory

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Extract the complete decoder frame from the exact genuine leaf
post-state and restored scratch arena already derived by leaf_normal. -/
theorem leaf_frame_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words parentWords : String→BitVec 64)
    (nodeArena : AllocatedBytes.Arena heap 64) (aligned : heap.toNat%8=0)
    (scratch : Rlp.Validation.Arena target cursor limit)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with memory:=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords))}) :
    NormalFrame source target heap cursor limit := by
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(PersistentAlloc.post source heap 64#64).globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be post
  change target.be=source.be at endian
  have codeEq:=congrArg PanSemStateFiniteExact.code post
  change target.code=source.code at codeEq
  have checked:=PersistentAlloc.guards heap 64#64 nodeArena.upper
  have grows : heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat:=checked.2.2.1
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0:=
    ⟨by have lower:=nodeArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  refine ⟨⟨_,?_,nextArena,checked.2.2.2.2,by omega⟩,⟨cursor,scratch,Nat.le_refl _⟩,domain,endian,codeEq,?_,?_⟩
  · rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · intro key notHeap notScratch
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]
  · intro query above below
    exact leaf_memory_of_post source target heap words parentWords nodeArena aligned post query (Or.inl below)

theorem extension_frame_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (scratch : Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {source with clock:=source.clock-1} .down cursor 88#64 with
        memory:=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields words))}) :
    NormalFrame source target heap cursor limit := by
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(Arenas.post source .down cursor 88#64).globals at globals
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write source.memory (LocalFields.writes (WitnessRecord.pointer cursor) (extensionFields words)) at memory
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be post
  change target.be=source.be at endian
  have codeEq:=congrArg PanSemStateFiniteExact.code post
  change target.code=source.code at codeEq
  have recordBounds:=WitnessRecord.allocation_bounds source cursor limit arena room
  refine ⟨⟨heap,?_,heapArena,heapAligned,Nat.le_refl _⟩,⟨_,scratch,by have upper:=recordBounds.2.2.1; omega⟩,domain,endian,codeEq,?_,?_⟩
  · rw [globals]
    simpa [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide] using heapCell
  · intro key notHeap notScratch
    rw [globals]
    simp [Arenas.post,Arenas.pointerName,HolFiniteMapExact.update,FUPDATE,Ne.symm notScratch]
  · intro query above below
    rw [memory]
    exact WitnessRecord.writes_above source cursor limit arena room (extensionFields words)
      (by intro field member; have bound:=extension_geometry words field member; omega) source.memory query above

theorem branch_frame_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (nodeArena : AllocatedBytes.Arena heap 176)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (scratch : Rlp.Validation.Arena target (WitnessRecord.pointer cursor) limit)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))}) :
    NormalFrame source target heap cursor limit := by
  have globals:=congrArg PanSemStateFiniteExact.globals post
  change target.globals=(Arenas.post (PersistentAlloc.post source heap 176#64) .down cursor 88#64).globals at globals
  have domain:=congrArg PanSemStateFiniteExact.memaddrs post
  change target.memaddrs=source.memaddrs at domain
  have endian:=congrArg PanSemStateFiniteExact.be post
  change target.be=source.be at endian
  have codeEq:=congrArg PanSemStateFiniteExact.code post
  change target.code=source.code at codeEq
  have checked:=PersistentAlloc.guards heap 176#64 nodeArena.upper
  have grows : heap.toNat+176≤(PersistentAlloc.rounded heap 176#64).toNat:=checked.2.2.1
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 176#64) 0:=
    ⟨by have lower:=nodeArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have recordBounds:=WitnessRecord.allocation_bounds source cursor limit arena room
  refine ⟨⟨_,?_,nextArena,checked.2.2.2.2,by omega⟩,⟨_,scratch,by have upper:=recordBounds.2.2.1; omega⟩,domain,endian,codeEq,?_,?_⟩
  · rw [globals]
    simp [Arenas.post,Arenas.pointerName,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,
      show ofString "scratch_ptr"≠ofString "heap_ptr" from by decide]
  · intro key notHeap notScratch
    rw [globals]
    simp [Arenas.post,Arenas.pointerName,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap,Ne.symm notScratch]
  · intro query above below
    exact branch_memory_of_post source target heap cursor limit words arena room nodeArena post query above (Or.inl below)

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_frame_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.extension_frame_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_frame_of_post
