import InitECandidate.Solver.Mpt.NewCurrent
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.Mpt.NewTrie
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem ready_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64)
    (arena : AllocatedBytes.Arena heap 16) :
    (ready source heap root secured).memory heap=.word root ∧
      (ready source heap root secured).memory (heap+8#64)=.word secured := by
  have number:=byteAddress_toNat heap 8 (by have h:=arena.upper; omega)
  change (heap+8#64).toNat=heap.toNat+8 at number
  have different : heap≠heap+8#64:=by intro same; have numeric:=congrArg BitVec.toNat same; omega
  simp [ready,rootStored,StoreWord.put,different]

theorem ready_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 16) (before : query.toNat<heap.toNat) :
    (ready source heap root secured).memory query=source.memory query := by
  have number:=byteAddress_toNat heap 8 (by have h:=arena.upper; omega)
  change (heap+8#64).toNat=heap.toNat+8 at number
  have awayRoot : query≠heap:=by intro same; subst query; omega
  have awaySecured : query≠heap+8#64:=by intro same; have numeric:=congrArg BitVec.toNat same; omega
  simp [ready,rootStored,allocated,StoreWord.put,awayRoot,awaySecured,WitnessRadix.QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite]

theorem ready_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64) :
    (ready source heap root secured).clock=source.clock-1 := rfl

theorem ready_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64) :
    (ready source heap root secured).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 16#64))) := by
  simp [ready,rootStored,allocated,WitnessRadix.QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem ready_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap root secured : BitVec 64) :
    HeapGlobals source (ready source heap root secured) := HeapGlobals.update source _

end InitECandidate.Solver.Mpt.NewTrie

#print axioms InitECandidate.Solver.Mpt.NewTrie.ready_cells
#print axioms InitECandidate.Solver.Mpt.NewTrie.ready_older
#print axioms InitECandidate.Solver.Mpt.NewTrie.ready_clock
#print axioms InitECandidate.Solver.Mpt.NewTrie.ready_heap
#print axioms InitECandidate.Solver.Mpt.NewTrie.ready_globals
