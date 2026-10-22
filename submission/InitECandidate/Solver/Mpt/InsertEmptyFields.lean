import InitECandidate.Solver.Mpt.InsertEmptyNormal

namespace InitECandidate.Solver.Mpt.Insert
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Physical fields and lifetime after the actual whole empty insertion.
All old words outside the fresh leaf survive; every leaf field, the true
next heap word and its aligned arena follow from the original run. -/
theorem empty_physical (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap key length pointer size : BitVec 64)
    (nodeCell : source.locals.lookup (ofString "node")=some (.val (.word 0#64)))
    (keyCell : source.locals.lookup (ofString "key")=some (.val (.word key)))
    (lengthCell : source.locals.lookup (ofString "klen")=some (.val (.word length)))
    (levelCell : source.locals.lookup (ofString "level")=some (.val (.word 0#64)))
    (pointerCell : source.locals.lookup (ofString "vptr")=some (.val (.word pointer)))
    (sizeCell : source.locals.lookup (ofString "vlen")=some (.val (.word size)))
    (installed : Input.OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    AllocatedBytes.Arena heap 64 ∧ value=.val (.word heap) ∧ source.clock-target.clock≤3 ∧
      target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 64#64))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0 ∧ (PersistentAlloc.rounded heap 64#64).toNat%8=0 ∧
      heap.toNat+64≤(PersistentAlloc.rounded heap 64#64).toNat ∧
      (∀ field∈NodeConstructor.fields .leaf (NodeConstructor.leafWords key length pointer size),
        target.memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word) ∧
      (∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+64≤query.toNat→target.memory query=source.memory query) := by
  obtain ⟨arena,answer,clock,cost,frame⟩:=empty_normal source target heap key length pointer size nodeCell keyCell lengthCell levelCell pointerCell sizeCell
    installed domain heapCell frontier aligned value normal
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap 64#64))) at globals
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=WordWrites.write source.memory (FieldStores.writes heap (NodeConstructor.fields .leaf (NodeConstructor.leafWords key length pointer size))) at memory
  have growth:=PersistentAlloc.guards heap 64#64 arena.upper
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap 64#64) 0:=
    ⟨by have lower:=arena.lower; have grows:=growth.2.2.1; omega,by have upper:=growth.2.2.2.1; omega⟩
  refine ⟨arena,answer,cost,globals,nextArena,growth.2.2.2.2,growth.2.2.1,?_,?_⟩
  · intro field member
    rw [memory]
    exact WordWrites.write_unique source.memory _ (heap+BitVec.ofNat 64 field.offset,field.value.word)
      (NodeConstructor.fields_distinct .leaf (NodeConstructor.leafWords key length pointer size) heap) (List.mem_map.mpr ⟨field,member,rfl⟩)
  · intro query outside
    rw [memory]
    let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,64⟩
    have valid : MutableTable.MemoryRegion.Valid region:=⟨arena.lower,arena.upper,aligned⟩
    have same : MutableTable.MemoryRegion.pointer region=heap:=by simp [MutableTable.MemoryRegion.pointer,region]
    rw [←same]
    exact FieldStores.writes_outside source.memory region valid (NodeConstructor.fields .leaf (NodeConstructor.leafWords key length pointer size))
      (fun field member=>(NodeConstructor.fields_geometry .leaf (NodeConstructor.leafWords key length pointer size) field member).1) query outside

end InitECandidate.Solver.Mpt.Insert

#print axioms InitECandidate.Solver.Mpt.Insert.empty_physical
