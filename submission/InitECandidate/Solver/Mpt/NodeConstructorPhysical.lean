import InitECandidate.Solver.Mpt.NodeConstructorAssigned
import InitECandidate.Solver.PanFieldStoresFrame

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical facts derived from actual scalar construction, shared by
callee returns and assigned calls with their caller locals restored. -/
structure Physical (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : String → BitVec 64) : Prop where
  arena : AllocatedBytes.Arena heap (bytes kind)
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  heapCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind)))))
  nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))) 0
  nextAligned : (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))).toNat%8=0
  before : heap.toNat+bytes kind≤(PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))).toNat
  cells : ∀ field∈fields kind words,target.memory (heap+BitVec.ofNat 64 field.offset)=.word field.value.word
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+bytes kind≤query.toNat → target.memory query=source.memory query

theorem physical_of_fields (kind : Kind) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : String → BitVec 64) (arena : AllocatedBytes.Arena heap (bytes kind)) (aligned : heap.toNat%8=0)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (globals : target.globals=source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))))))
    (memory : target.memory=WordWrites.write source.memory (FieldStores.writes heap (fields kind words))) :
    Physical kind source target heap words := by
  have amount : (BitVec.ofNat 64 (bytes kind)).toNat=bytes kind:=by cases kind <;> rfl
  have growth:=rounded_ordinary heap (BitVec.ofNat 64 (bytes kind)) (by rw [amount]; exact arena.upper)
  rw [amount] at growth
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))) 0:=
    ⟨by have first:=arena.lower; have grows:=growth.1; omega,by have last:=growth.2.1; omega⟩
  refine ⟨arena,domain,endian,?_,nextArena,growth.2.2,growth.1,?_,?_⟩
  · rw [globals]
    simp [HolFiniteMapExact.update,FUPDATE]
  · intro field member
    rw [memory]
    exact WordWrites.write_unique source.memory _ (heap+BitVec.ofNat 64 field.offset,field.value.word)
      (fields_distinct kind words heap) (List.mem_map.mpr ⟨field,member,rfl⟩)
  · intro query outside
    rw [memory]
    let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,bytes kind⟩
    have valid : MutableTable.MemoryRegion.Valid region:=⟨arena.lower,arena.upper,aligned⟩
    have same : MutableTable.MemoryRegion.pointer region=heap:=by simp [MutableTable.MemoryRegion.pointer,region]
    rw [←same]
    exact FieldStores.writes_outside source.memory region valid (fields kind words) (fun field member=>(fields_geometry kind words field member).1) query outside

theorem scalar_physical (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String → BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    value=.val (.word heap) ∧ Physical kind source target heap words := by
  obtain ⟨answer,nodeArena,positive,frame⟩:=scalar_normal_from_arena kind scalar source target heap words inputs domain heapCell arena aligned installed value normal
  exact ⟨answer,physical_of_fields kind source target heap words nodeArena aligned
    (by have same:=congrArg PanSemStateFiniteExact.memaddrs frame; exact same) (by have same:=congrArg PanSemStateFiniteExact.be frame; exact same)
    (congrArg PanSemStateFiniteExact.globals frame) (congrArg PanSemStateFiniteExact.memory frame)⟩

theorem assigned_physical (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String → BitVec 64)
    (name : MlS) (arguments : List (ExpHOL 64)) (values : List (ValueHOL 64)) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (argsRead : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some values)
    (expectedCall : lookupCodeHOLFinite source.code.lookup (ofString (NodeConstructor.name kind)) values=some (body kind,callee,.one))
    (inputs : Inputs kind (callEntryStateHOLFinite source callee) words)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source (.call (some (some (.local,name),none)) (ofString (NodeConstructor.name kind)) arguments)=(none,target)) :
    Physical kind source target heap words := by
  obtain ⟨arena,frame⟩:=assigned_normal kind scalar source target heap words name arguments values callee argsRead expectedCall inputs domain heapCell frontier aligned installed normal
  exact physical_of_fields kind source target heap words arena aligned
    (by have same:=congrArg PanSemStateFiniteExact.memaddrs frame; exact same) (by have same:=congrArg PanSemStateFiniteExact.be frame; exact same)
    (congrArg PanSemStateFiniteExact.globals frame) (congrArg PanSemStateFiniteExact.memory frame)

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.physical_of_fields
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_physical
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.assigned_physical
