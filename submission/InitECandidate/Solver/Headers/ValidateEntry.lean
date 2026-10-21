import InitECandidate.Solver.Headers.ValidateAllocation

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

def entryHeap (heap count : BitVec 64) := PersistentAlloc.rounded (hashesPointer heap count) (hashesSize count)

theorem loopEntry_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64)
    (key : MlS) (notHeap : key≠ofString "heap_ptr") :
    (loopEntry source heap count).globals.lookup key=source.globals.lookup key := by
  simp [loopEntry,hashesSource,hsSource,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap]

theorem loopEntry_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) :
    (loopEntry source heap count).globals.lookup (ofString "heap_ptr")=some (.val (.word (entryHeap heap count))) := by
  simp [loopEntry,hashesSource,hsSource,entryHeap,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.lookup_update,FUPDATE]

theorem loopEntry_arena (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) : Rlp.Validation.Arena (loopEntry source heap count) cursor limit :=
  ⟨arena.domain,(loopEntry_globals source heap count _ (by decide)).trans arena.cursorGlobal,
    (loopEntry_globals source heap count _ (by decide)).trans arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩

theorem loopEntry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count array : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word count))) :
    (loopEntry source heap count).locals.lookup (ofString "arr")=some (.val (.word array)) ∧
    (loopEntry source heap count).locals.lookup (ofString "n")=some (.val (.word count)) ∧
    (loopEntry source heap count).locals.lookup (ofString "hs")=some (.val (.word heap)) ∧
    (loopEntry source heap count).locals.lookup (ofString "hashes")=some (.val (.word (hashesPointer heap count))) ∧
    (loopEntry source heap count).locals.lookup (ofString "i")=some (.val (.word 0#64)) := by
  simp [loopEntry,hashesSource,hsSource,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,arrayCell,countCell,ofString]
  exact ⟨arrayCell,countCell⟩

theorem loopEntry_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap count : BitVec 64) :
    (loopEntry source heap count).clock=source.clock-2 := by
  simp [loopEntry,hashesSource,hsSource,WitnessRadix.QueryBranch.bind,setVarHOLFinite,PersistentAlloc.post,Nat.sub_sub]

/-- Physical geometry comes from the two actual original allocator room
facts. The extra one-element capacities also cover the zero-header case. -/
structure Geometry (heap count : BitVec 64) : Prop where
  hs : AllocatedBytes.Arena heap (8*count.toNat+8)
  hsAligned : heap.toNat%8=0
  hashes : AllocatedBytes.Arena (hashesPointer heap count) (32*count.toNat+32)
  hashesAligned : (hashesPointer heap count).toNat%8=0
  hsBefore : heap.toNat+8*count.toNat+8≤(hashesPointer heap count).toNat
  hashesBefore : (hashesPointer heap count).toNat+32*count.toNat+32≤(entryHeap heap count).toNat
  heapBound : (entryHeap heap count).toNat≤33806089496
  heapAligned : (entryHeap heap count).toNat%8=0

theorem geometry_of_room (heap count : BitVec 64) (small : count.toNat≤256)
    (lower : 2701131776≤heap.toNat) (aligned : heap.toNat%8=0)
    (firstRoom : heap.toNat+(hsSize count).toNat≤33806089496)
    (secondRoom : (hashesPointer heap count).toNat+(hashesSize count).toNat≤33806089496) : Geometry heap count := by
  have numbers:=size_numbers count small
  have first:=PersistentAlloc.guards heap (hsSize count) firstRoom
  have second:=PersistentAlloc.guards (hashesPointer heap count) (hashesSize count) secondRoom
  have hsBefore : heap.toNat+8*count.toNat+8≤(hashesPointer heap count).toNat := by
    have h:=first.2.2.1
    rw [numbers.1] at h
    change heap.toNat+(8*count.toNat+8)≤(hashesPointer heap count).toNat at h
    omega
  have hashesBefore : (hashesPointer heap count).toNat+32*count.toNat+32≤(entryHeap heap count).toNat := by
    have h:=second.2.2.1
    rw [numbers.2] at h
    change (hashesPointer heap count).toNat+(32*count.toNat+32)≤(entryHeap heap count).toNat at h
    omega
  refine ⟨⟨lower,by rw [numbers.1] at firstRoom; omega⟩,aligned,⟨by omega,by rw [numbers.2] at secondRoom; omega⟩,first.2.2.2.2,
    hsBefore,hashesBefore,second.2.2.2.1,second.2.2.2.2⟩

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.loopEntry_globals
#print axioms InitECandidate.Solver.Headers.Validate.loopEntry_heap
#print axioms InitECandidate.Solver.Headers.Validate.loopEntry_arena
#print axioms InitECandidate.Solver.Headers.Validate.loopEntry_cells
#print axioms InitECandidate.Solver.Headers.Validate.loopEntry_clock
#print axioms InitECandidate.Solver.Headers.Validate.geometry_of_room
