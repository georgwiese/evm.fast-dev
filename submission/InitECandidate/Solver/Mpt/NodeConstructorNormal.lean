import InitECandidate.Solver.Mpt.NodeConstructorFields
import InitECandidate.Solver.Mpt.NodeConstructorCost
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine normal scalar constructor returns the previous heap word,
derives its own allocation room and performs exactly the original field
writes. Every other nonlocal field is retained by the exact post-state. -/
theorem scalar_normal (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    value=.val (.word heap) ∧ AllocatedBytes.Arena heap (bytes kind) ∧ 1≤source.clock ∧
    emptyLocalsHOLFinite target=emptyLocalsHOLFinite
      {PersistentAlloc.post {source with clock:=source.clock-1} heap (BitVec.ofNat 64 (bytes kind)) with
        memory:=WordWrites.write source.memory (FieldStores.writes heap (fields kind words))} := by
  have amountNumber : (BitVec.ofNat 64 (bytes kind)).toNat=bytes kind := by cases kind <;> rfl
  have args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) [.const (BitVec.ofNat 64 (bytes kind))]=
      some (PersistentAlloc.values (BitVec.ofNat 64 (bytes kind))) := rfl
  rw [allocation_shape] at normal
  obtain ⟨room,positive,inner,tailRun,endpoint⟩:=PersistentAlloc.call_normal source target "nd" [.const (BitVec.ofNat 64 (bytes kind))] (tail kind)
    heap (BitVec.ofNat 64 (bytes kind)) args (PersistentAlloc.original_code source.code installed) (Input.Trap.original_code source.code installed)
    heapCell (by have upper:=arena.upper; omega) value normal
  rw [amountNumber] at room
  have nodeArena : AllocatedBytes.Arena heap (bytes kind):=⟨arena.lower,room⟩
  let ready:=QueryBranch.bind (PersistentAlloc.post {source with clock:=source.clock-1} heap (BitVec.ofNat 64 (bytes kind))) "nd" heap
  have currentInputs:=inputs_allocation kind source words heap (BitVec.ofNat 64 (bytes kind)) inputs
  have currentNode : ready.locals.lookup (ofString "nd")=some (.val (.word heap)):=QueryBranch.bind_lookup_same _ _ _
  have mapped (field : FieldStores.Field) (inside : field∈fields kind words) : ready.memaddrs (heap+BitVec.ofNat 64 field.offset) :=
    AllocatedBytes.word_mapped ready heap (bytes kind) field.offset domain nodeArena (fields_geometry kind words field inside).1 aligned (fields_geometry kind words field inside).2
  have writes:=FieldStores.execute ready "nd" "" heap 0#64 (fields kind words) currentNode (fields_ready kind ready words currentInputs) mapped
    (fun reader readerIn writer writerIn=>fields_avoid kind words 0#64 _ reader readerIn) (.return (QueryBranch.localVar "nd"))
  rw [scalar_tail_shape kind scalar words,writes] at tailRun
  obtain ⟨read,innerEq⟩:=Input.return_normal _ inner (QueryBranch.localVar "nd") value tailRun
  have expected : QueryBranch.eval {ready with memory:=WordWrites.write ready.memory (FieldStores.writes heap (fields kind words))}
      (QueryBranch.localVar "nd")=some (.val (.word heap)) := by
    simp [QueryBranch.eval,QueryBranch.localVar,evalHOLExact,toExact,currentNode]
  have valueEq : value=.val (.word heap):=Option.some.inj (read.symm.trans expected)
  refine ⟨valueEq,nodeArena,positive,?_⟩
  rw [endpoint,innerEq]
  rfl

/-- The real scalar constructor writes only within its newly allocated
node region; all old scratch records, tables and earlier heap cells survive. -/
theorem scalar_normal_frame (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+bytes kind≤query.toNat→target.memory query=source.memory query := by
  obtain ⟨valueEq,nodeArena,positive,frame⟩:=scalar_normal kind scalar source target heap words inputs domain heapCell arena aligned installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=WordWrites.write source.memory (FieldStores.writes heap (fields kind words)) at memory
  let region : MutableTable.MemoryRegion.Region:=⟨heap.toNat,bytes kind⟩
  have valid : MutableTable.MemoryRegion.Valid region:=⟨nodeArena.lower,nodeArena.upper,aligned⟩
  intro query outside
  rw [memory]
  have pointerEq : MutableTable.MemoryRegion.pointer region=heap:=by simp [MutableTable.MemoryRegion.pointer,region]
  rw [←pointerEq]
  exact FieldStores.writes_outside source.memory region valid (fields kind words) (fun field inside=>(fields_geometry kind words field inside).1) query outside

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_normal
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_normal_frame
