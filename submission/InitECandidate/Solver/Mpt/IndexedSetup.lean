import InitECandidate.Solver.Mpt.IndexedProgram
import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Input.HeapMarkPrefix
import InitECandidate.Solver.Input.CallPrefixDeclaration

namespace InitECandidate.Solver.Mpt.Indexed
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def marked (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  Input.CallPrefix.heapMarked source (ofString "mark") heap
def newEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  setVarHOLFinite (ofString "m") (.val (.word heap)) (NewTrie.post (marked source heap) heap 0#64 0#64)
def loopEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  bind (newEntry source heap) "i" 0#64

/-- Original heap_mark, mpt_new(0,0) and i=0 supply the real fresh,
unsecured empty trie before the indexed builder's unsigned loop. -/
theorem setup_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (execution : Input.CallPrefix.Execution source actions current) :
    AllocatedBytes.Arena heap 16 ∧ current=loopEntry source heap := by
  change Input.CallPrefix.Execution source
    (.scoped (ofString "mark") .one (ofString "heap_mark") []::
      .scoped (ofString "m") .one (ofString "mpt_new") [.const 0#64,.const 0#64]::
      .declare (ofString "i") .one (.const 0#64)::[]) current at execution
  have afterMark:=execution.heap_mark_next (ofString "mark") heap _ installed heapCell
  have args : evalListHOLFinite (marked source heap) (h:=fun address=>Classical.propDecidable ((marked source heap).memaddrs address))
      [.const 0#64,.const 0#64]=some (NewTrie.values 0#64 0#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,NewTrie.values]
  obtain ⟨arena,afterNew⟩:=NewTrie.scoped_next (source:=marked source heap) (target:=current) (ofString "m") [.const 0#64,.const 0#64]
    heap 0#64 0#64 [.declare (ofString "i") .one (.const 0#64)] installed args heapCell domain frontier aligned afterMark
  have last:=afterNew.declare_next (.val (.word 0#64)) rfl
  have same : current=loopEntry source heap:=by cases last; rfl
  exact ⟨arena,same⟩

theorem normal_setup (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (domain : source.memaddrs=InitE.ordinaryDomain) (frontier : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    AllocatedBytes.Arena heap 16 ∧ ∃ inner,post.clock=inner.clock ∧
      evaluateHOLFiniteState (loopEntry source heap) loopAndAfter=(some (.returned value),inner) := by
  obtain ⟨current,inner,execution,endpoint,remaining⟩:=setup_trace source post value normal
  obtain ⟨arena,same⟩:=setup_from_execution source current heap installed heapCell domain frontier aligned execution
  rw [same] at remaining
  exact ⟨arena,inner,endpoint,remaining⟩

theorem loop_entry_clock (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (loopEntry source heap).clock=source.clock-3 := by
  simp only [loopEntry,newEntry,marked,Input.CallPrefix.heapMarked,NewTrie.post,QueryBranch.bind,setVarHOLFinite,Nat.sub_sub]

theorem loop_entry_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (arena : AllocatedBytes.Arena heap 16) :
    (loopEntry source heap).memory heap=.word 0#64 ∧ (loopEntry source heap).memory (heap+8#64)=.word 0#64 :=
  NewTrie.post_cells (marked source heap) heap 0#64 0#64 arena

theorem loop_entry_older (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap query : BitVec 64)
    (arena : AllocatedBytes.Arena heap 16) (before : query.toNat<heap.toNat) :
    (loopEntry source heap).memory query=source.memory query := NewTrie.post_older (marked source heap) heap 0#64 0#64 query arena before

theorem loop_entry_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (loopEntry source heap).locals.lookup (ofString "m")=some (.val (.word heap)) ∧
      (loopEntry source heap).locals.lookup (ofString "i")=some (.val (.word 0#64)) := by
  simp [loopEntry,newEntry,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem loop_entry_mark (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (loopEntry source heap).locals.lookup (ofString "mark")=some (.val (.word heap)) := by
  simp [loopEntry,newEntry,marked,Input.CallPrefix.heapMarked,NewTrie.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ofString]

theorem loop_entry_saved (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (key : MlS)
    (otherMark : ofString "mark"≠key) (otherM : ofString "m"≠key) (otherI : ofString "i"≠key) :
    (loopEntry source heap).locals.lookup key=source.locals.lookup key := by
  simp [loopEntry,newEntry,marked,Input.CallPrefix.heapMarked,NewTrie.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,otherMark,otherM,otherI]

theorem loop_entry_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (arena : AllocatedBytes.Arena heap 16) :
    (loopEntry source heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap 16#64))) ∧
      AllocatedBytes.Arena (PersistentAlloc.rounded heap 16#64) 0 ∧ (PersistentAlloc.rounded heap 16#64).toNat%8=0 ∧
      heap.toNat+16≤(PersistentAlloc.rounded heap 16#64).toNat := by
  have growth:=NodeConstructor.rounded_ordinary heap 16#64 arena.upper
  refine ⟨?_,⟨by have h:=arena.lower; have g:=growth.1; omega,by have h:=growth.2.1; omega⟩,growth.2.2,growth.1⟩
  simp [loopEntry,newEntry,NewTrie.post,QueryBranch.bind,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]

theorem loop_entry_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    HeapGlobals source (loopEntry source heap) := HeapGlobals.update source _

end InitECandidate.Solver.Mpt.Indexed

#print axioms InitECandidate.Solver.Mpt.Indexed.setup_from_execution
#print axioms InitECandidate.Solver.Mpt.Indexed.normal_setup
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_clock
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_cells
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_older
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_locals
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_mark
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_saved
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_heap
#print axioms InitECandidate.Solver.Mpt.Indexed.loop_entry_globals
