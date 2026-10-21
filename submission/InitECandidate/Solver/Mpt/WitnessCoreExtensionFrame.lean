import InitECandidate.Solver.Mpt.WitnessCoreExtensionReturn
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame
import InitECandidate.Solver.Mpt.NodeConstructorCells

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The actual extension allocation and subsequent parent stores touch
only its fresh node. Every earlier heap word and live scratch record is
retained, including through the original ck/ex scope restorations. -/
theorem extension_finished_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (nodeArena : AllocatedBytes.Arena heap 56) (aligned : heap.toNat%8=0)
    (query : BitVec 64) (before : query.toNat<heap.toNat) :
    (extensionFinishedState source heap nibbles length child previous kind data).memory query=source.memory query := by
  let ready:=QueryBranch.bind (extensionAllocated (QueryBranch.bind source "ck" kind) heap nibbles length child) "ex" heap
  change (metadataState ready heap data.pointer data.length previous).memory query=source.memory query
  have upper:=nodeArena.upper
  have number8 : (heap+8#64).toNat=heap.toNat+8:=byteAddress_toNat heap 8 (by omega)
  have number16 : (heap+16#64).toNat=heap.toNat+16:=byteAddress_toNat heap 16 (by omega)
  have away8 : query≠heap+8#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number8] at number; omega
  have away16 : query≠heap+16#64:=by intro same; have number:=congrArg BitVec.toNat same; rw [number16] at number; omega
  rw [metadata_memory ready heap data.pointer data.length previous query away8 away16]
  change WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child))) query=source.memory query
  let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,56⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨nodeArena.lower,nodeArena.upper,aligned⟩
  have pointerEq : MutableTable.MemoryRegion.pointer region=heap:=by simp [MutableTable.MemoryRegion.pointer,region]
  rw [←pointerEq]
  exact FieldStores.writes_outside source.memory region valid (NodeConstructor.fields .extension (extensionWords nibbles length child))
    (fun field member=>(NodeConstructor.fields_geometry .extension _ field member).1) query (Or.inl before)

/-- The real extension return supplies the same complete old-storage
frame used by the decoder: exact next heap, restored scratch, immutable
domain/endian/code and all nonheap globals. This can frame older active
records and the fixed witness databases at their own allocation frontier. -/
theorem extension_finished_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (nodeArena : AllocatedBytes.Arena heap 56) (aligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) :
    WitnessDecode.NormalFrame source (extensionFinishedState source heap nibbles length child previous kind data) heap cursor limit := by
  let target:=extensionFinishedState source heap nibbles length child previous kind data
  have globals : target.globals=(PersistentAlloc.post source heap 56#64).globals:=rfl
  have checked:=PersistentAlloc.guards heap 56#64 nodeArena.upper
  have grows : heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat:=checked.2.2.1
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 56#64) 0:=
    ⟨by have lower:=nodeArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have others (key : MlS) (notHeap : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key:=by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]
  have scratch : Rlp.Validation.Arena target cursor limit:=
    ⟨arena.domain,(others _ (by decide)).trans arena.cursorGlobal,(others _ (by decide)).trans arena.limitGlobal,
      arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  refine ⟨⟨PersistentAlloc.rounded heap 56#64,?_,nextArena,checked.2.2.2.2,by omega⟩,
    ⟨cursor,scratch,Nat.le_refl _⟩,rfl,rfl,rfl,?_,?_⟩
  · rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  · intro key notHeap notScratch
    exact others key notHeap
  · intro query above below
    exact extension_finished_memory source heap nibbles length child previous kind data nodeArena aligned query below

theorem extension_finished_tag (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description) :
    (extensionFinishedState source heap nibbles length child previous kind data).memory heap=.word 2#64 := by
  let ready:=QueryBranch.bind (extensionAllocated (QueryBranch.bind source "ck" kind) heap nibbles length child) "ex" heap
  change (metadataState ready heap data.pointer data.length previous).memory heap=.word 2#64
  have away8 : heap≠heap+8#64:=by
    intro same
    have equal : (0#64 : BitVec 64)=8#64:=(BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using same)
    exact (by decide : (0#64 : BitVec 64)≠8#64) equal
  have away16 : heap≠heap+16#64:=by
    intro same
    have equal : (0#64 : BitVec 64)=16#64:=(BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using same)
    exact (by decide : (0#64 : BitVec 64)≠16#64) equal
  rw [metadata_memory ready heap data.pointer data.length previous heap away8 away16]
  change WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child))) heap=.word 2#64
  have member : (heap,2#64)∈FieldStores.writes heap (NodeConstructor.fields .extension (extensionWords nibbles length child)):=by
    simp [FieldStores.writes,NodeConstructor.fields,FieldStores.Value.word]
  exact WordWrites.write_unique source.memory _ (heap,2#64) (NodeConstructor.fields_distinct .extension _ heap) member

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_frame
#print axioms InitECandidate.Solver.Mpt.WitnessCore.extension_finished_tag
