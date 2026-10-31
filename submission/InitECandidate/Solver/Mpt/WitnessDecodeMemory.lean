import InitECandidate.Solver.Mpt.WitnessDecodeBranchNormal
import InitECandidate.Solver.Mpt.WitnessDecodeLeafNormal
import InitECandidate.Solver.Mpt.WitnessRecordMemory
import InitECandidate.Solver.Mpt.NodeConstructorCells
import InitECandidate.Solver.PanFieldStoresFrame

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Extract the protected old-memory band from the exact post-state already
derived by branch_normal. Only the fresh node and the new record can change. -/
theorem branch_memory_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (nodeArena : AllocatedBytes.Arena heap 176)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))}) :
    ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<heap.toNat ∨ heap.toNat+176≤query.toNat→target.memory query=source.memory query := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words)) at memory
  intro query above outside
  have recordAway:=WitnessRecord.writes_above source cursor limit arena room (branchFields words)
    (by intro field member; have bound:=branch_geometry words field member; omega) (branchAllocated source heap).memory query above
  rw [memory,recordAway]
  change StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64 query=source.memory query
  have tagAway : query≠heap:=by intro same; subst query; omega
  rw [StoreWord.put,if_neg tagAway]
  apply Zero.final_memory_away
  intro offset inside same
  have numeric:=congrArg BitVec.toNat same
  rw [byteAddress_toNat heap offset (by have bound:=nodeArena.upper; omega)] at numeric
  omega

theorem branch_tag_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (below : cursor.toNat≤heap.toNat)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))}) :
    target.memory heap=.word 3#64 := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words)) at memory
  have recordAway:=WitnessRecord.writes_above source cursor limit arena room (branchFields words)
    (by intro field member; have bound:=branch_geometry words field member; omega) (branchAllocated source heap).memory heap below
  rw [memory,recordAway]
  exact if_pos rfl

/-- The actual branch writes only its new persistent node and its new
scratch record. This protects both sides of the current live scratch band. -/
theorem branch_memory_outside_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (nodeArena : AllocatedBytes.Arena heap 176)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))}) :
    ∀ query : BitVec 64,(query.toNat<limit.toNat ∨ cursor.toNat≤query.toNat)→
      (query.toNat<heap.toNat ∨ heap.toNat+176≤query.toNat)→target.memory query=source.memory query := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words)) at memory
  intro query scratchOutside nodeOutside
  have recordAway:=WitnessRecord.writes_outside source cursor limit arena room (branchFields words)
    (by intro field member; have bound:=branch_geometry words field member; omega) (branchAllocated source heap).memory query scratchOutside
  rw [memory,recordAway]
  change StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64 query=source.memory query
  have tagAway : query≠heap:=by intro same; subst query; omega
  rw [StoreWord.put,if_neg tagAway]
  apply Zero.final_memory_away
  intro offset inside same
  have numeric:=congrArg BitVec.toNat same
  rw [byteAddress_toNat heap offset (by have bound:=nodeArena.upper; omega)] at numeric
  omega

/-- The branch tag is below the live scratch limit, so the subsequent
record stores cannot overwrite the actual constructor's kind word. -/
theorem branch_tag_below_limit_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (words : String→BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (room : Arenas.Room .down cursor limit 88#64)
    (below : heap.toNat<limit.toNat)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {Arenas.post {branchAllocated source heap with clock:=source.clock-11} .down cursor 88#64 with
        memory:=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words))}) :
    target.memory heap=.word 3#64 := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields words)) at memory
  have recordAway:=WitnessRecord.writes_outside source cursor limit arena room (branchFields words)
    (by intro field member; have bound:=branch_geometry words field member; omega) (branchAllocated source heap).memory heap (Or.inl below)
  rw [memory,recordAway]
  exact if_pos rfl

/-- Leaf construction and its original parent p/n metadata overwrite both
stay inside the fresh64-byte arena from the genuine normal allocation. -/
theorem leaf_memory_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words parentWords : String→BitVec 64)
    (nodeArena : AllocatedBytes.Arena heap 64) (aligned : heap.toNat%8=0)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with
        memory:=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords))}) :
    ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat→target.memory query=source.memory query := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords)) at memory
  let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,64⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨nodeArena.lower,nodeArena.upper,aligned⟩
  intro query outside
  have metaAway:=LocalFields.writes_outside (leafAllocated source heap words).memory region valid (leafFields parentWords)
    (by intro field member; change field.offset<64; have bound:=leaf_geometry parentWords field member; omega) query outside
  have constructorAway:=FieldStores.writes_outside source.memory region valid (NodeConstructor.fields .leaf words)
    (by intro field member; exact (NodeConstructor.fields_geometry .leaf words field member).1) query outside
  simp only [region,MutableTable.MemoryRegion.pointer,BitVec.ofNat_toNat,BitVec.setWidth_eq] at metaAway constructorAway
  rw [memory,metaAway]
  exact constructorAway

theorem leaf_tag_of_post (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words parentWords : String→BitVec 64)
    (post : emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {leafAllocated source heap words with
        memory:=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords))}) :
    target.memory heap=.word 1#64 := by
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (leafAllocated source heap words).memory (LocalFields.writes heap (leafFields parentWords)) at memory
  have offset8 : heap+8#64≠heap:=by
    intro same
    have impossible : (8#64 : BitVec 64)=0#64:=(BitVec.add_right_inj heap).1 (by simpa only [BitVec.add_zero] using same)
    exact (by decide : (8#64 : BitVec 64)≠0#64) impossible
  have offset16 : heap+16#64≠heap:=by
    intro same
    have impossible : (16#64 : BitVec 64)=0#64:=(BitVec.add_right_inj heap).1 (by simpa only [BitVec.add_zero] using same)
    exact (by decide : (16#64 : BitVec 64)≠0#64) impossible
  have away : heap∉(LocalFields.writes heap (leafFields parentWords)).map Prod.fst:=by
    simp [LocalFields.writes,leafFields,Ne.symm offset8,Ne.symm offset16]
  rw [memory,WordWrites.write_away _ _ heap away]
  change WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf words)) heap=.word 1#64
  have tag:=WordWrites.write_unique source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf words)) (heap+0#64,1#64)
    (NodeConstructor.fields_distinct .leaf words heap) (by simp [FieldStores.writes,NodeConstructor.fields,FieldStores.Value.word])
  simpa only [BitVec.add_zero] using tag

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_memory_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_tag_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_memory_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.leaf_tag_of_post

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_memory_outside_of_post
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_tag_below_limit_of_post
