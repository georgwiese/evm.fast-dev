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
    (query : BitVec 64) (outside : query.toNat<heap.toNat ∨ heap.toNat+56≤query.toNat) :
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
  apply WordWrites.write_away
  intro member
  simp only [FieldStores.writes,List.map_map,Function.comp_def] at member
  obtain ⟨field,inFields,same⟩:=List.mem_map.mp member
  have small:=(NodeConstructor.fields_geometry .extension (extensionWords nibbles length child) field inFields).1
  change field.offset<56 at small
  have number : (heap+BitVec.ofNat 64 field.offset).toNat=heap.toNat+field.offset:=
    byteAddress_toNat heap field.offset (by omega)
  have equal:=congrArg BitVec.toNat same
  rw [number] at equal
  omega

/-- The actual extension return writes only the newly allocated node.
Its returned allocator room proves the persistent cap; the live scratch
geometry then protects every older record above the incoming cursor. -/
theorem extension_finished_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit nibbles length child previous kind : BitVec 64) (data : WitnessRecord.Description)
    (nodeArena : AllocatedBytes.Arena heap 56) (room : heap.toNat+56≤2952790016) (aligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) :
    WitnessDecode.LiveFrame source (extensionFinishedState source heap nibbles length child previous kind data) heap cursor limit := by
  let target:=extensionFinishedState source heap nibbles length child previous kind data
  have globals : target.globals=(PersistentAlloc.post source heap 56#64).globals:=rfl
  have checked:=PersistentAlloc.guards heap 56#64 room
  have grows : heap.toNat+56≤(PersistentAlloc.rounded heap 56#64).toNat:=checked.2.2.1
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 56#64) 0:=
    ⟨by have lower:=nodeArena.lower; omega,by have upper:=checked.2.2.2.1; omega⟩
  have others (key : MlS) (notHeap : key≠ofString "heap_ptr") : target.globals.lookup key=source.globals.lookup key:=by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm notHeap]
  have persistent : Input.PersistentNormalFrame source target heap:=by
    refine ⟨⟨PersistentAlloc.rounded heap 56#64,?_,nextArena,checked.2.2.2.1,checked.2.2.2.2,by omega⟩,
      rfl,others,?_⟩
    · rw [globals]
      simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
    · intro query before
      exact extension_finished_memory source heap nibbles length child previous kind data nodeArena aligned query (Or.inl before)
  apply WitnessDecode.LiveFrame.of_persistent source target heap cursor limit live arena persistent
  intro query above
  have lower:=(live.bounds arena).1
  have ordered:=arena.ordered
  exact extension_finished_memory source heap nibbles length child previous kind data nodeArena aligned query (Or.inr (by omega))

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
