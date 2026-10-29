import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderOmmer
import InitECandidate.Solver.CurrentKeccak.Call
import InitECandidate.Solver.WitnessRadix.CopyAwayIntervals

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- These rooms are obtained from the actual three allocations, not merely
from readable ordinary-memory addresses. -/
structure OmmerLayout (heap : BitVec 64) : Prop where
  headerArena : AllocatedBytes.Arena heap 248
  headerRoom : heap.toNat+248≤2952790016
  headerAligned : heap.toNat%8=0
  ommerArena : AllocatedBytes.Arena (ommerBase heap) 32
  ommerRoom : (ommerBase heap).toNat+32≤2952790016
  temporaryArena : AllocatedBytes.Arena (temporaryBase heap) 8
  temporaryRoom : (temporaryBase heap).toNat+8≤2952790016
  ommerAligned : (ommerBase heap).toNat%8=0
  temporaryAligned : (temporaryBase heap).toNat%8=0
  headerBefore : heap.toNat+248≤(ommerBase heap).toNat
  ommerBefore : (ommerBase heap).toNat+32≤(temporaryBase heap).toNat

theorem marked_ommer_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (key : MlS) (other : key≠ofString "heap_ptr") :
    (markedOmmer source pointer record heap).globals.lookup key=source.globals.lookup key := by
  simp [markedOmmer,temporaryAllocated,ommerAllocated,firstStored,putHeader,clearedHeader,headerEntry,readEntry,
    QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,Ne.symm other]

theorem marked_ommer_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64) :
    CurrentKeccak.Hash.Environment (markedOmmer source pointer record heap) 2701132160#64 2701132360#64 :=
  ⟨environment.installed,environment.domain,
    (marked_ommer_globals source pointer record heap _ (by decide)).trans environment.stateGlobal,
    (marked_ommer_globals source pointer record heap _ (by decide)).trans environment.padGlobal,
    environment.stateArena,environment.padArena,environment.stateAligned,environment.padAligned⟩

structure OmmerHashOutput (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (target : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  normal : evaluateHOLFiniteState (markedOmmer source pointer record heap) hashOmmer=(none,target)
  locals : ∀ key,target.locals.lookup key=(markedOmmer source pointer record heap).locals.lookup key
  globals : ∀ key,target.globals.lookup key=(markedOmmer source pointer record heap).globals.lookup key
  environment : CurrentKeccak.Hash.Environment target 2701132160#64 2701132360#64
  price : (markedOmmer source pointer record heap).clock-target.clock≤690
  memory : ∀ query,2701134824≤query.toNat→query.toNat<(ommerBase heap).toNat→
    target.memory query=(markedOmmer source pointer record heap).memory query

/-- The actual current 24-round software hash returns to its original
continuation and protects the fresh header and earlier copied input. -/
theorem ommer_hash_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (environment : CurrentKeccak.Hash.Environment source 2701132160#64 2701132360#64) (layout : OmmerLayout heap)
    (execution : CallPrefix.Execution (temporaryAllocated source pointer record heap) afterOmmerBuffers current) :
    ∃ hashed,OmmerHashOutput source pointer record heap hashed ∧ CallPrefix.Execution hashed afterOmmerHash current := by
  have markedExecution:=ommer_marker_from_execution source current pointer record heap environment.domain layout.temporaryArena execution
  obtain ⟨hashed,normal,next⟩:=markedExecution.command_next hashOmmer afterOmmerHash
  let marked:=markedOmmer source pointer record heap
  have tmpCell : marked.locals.lookup (ofString "tmp")=some (.val (.word (temporaryBase heap))):=temporary_local source pointer record heap
  have ohCell : marked.locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))):=ommer_local source pointer record heap
  have args : evalListHOLFinite marked (h:=fun address=>Classical.propDecidable (marked.memaddrs address))
      [localVar "tmp",.const 1#64,localVar "oh"]=some (CurrentKeccak.Hash.values (temporaryBase heap) (ommerBase heap) 1):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,tmpCell,ohCell,CurrentKeccak.Hash.values]
  have ready:=marked_ommer_environment source pointer record heap environment
  have inputArena : AllocatedBytes.Arena (temporaryBase heap) 1:=layout.temporaryArena.weaken _ 8 1 (by decide)
  have kept (key : MlS) : hashed.globals.lookup key=marked.globals.lookup key := by
    have proof:=CurrentKeccak.Hash.call_globals key marked.code ready.installed [localVar "tmp",.const 1#64,localVar "oh"] marked rfl
    change GlobalEffects.erase key (evaluateHOLFiniteState marked hashOmmer).2=GlobalEffects.erase key marked at proof
    rw [normal] at proof
    exact congrArg Prod.snd proof
  have price:=CurrentKeccak.Hash.call_cost marked [localVar "tmp",.const 1#64,localVar "oh"] (temporaryBase heap) (ommerBase heap) 1 (by decide) ready.installed args
  change marked.clock-(evaluateHOLFiniteState marked hashOmmer).2.clock≤690 at price
  rw [normal] at price
  refine ⟨hashed,⟨normal,?_,kept,ready.after hashOmmer none (fun key=>CurrentKeccak.Hash.call_globals key marked.code ready.installed _) normal,price,?_⟩,next⟩
  · intro key
    exact CallNormal.ignored_lookup marked hashed key (ofString "keccak256") _ normal
  · intro query lower before
    exact (CurrentKeccak.Hash.call_frame marked hashed _ _ _ _ query 1 ready _ args inputArena layout.ommerArena
      (CopyGeneral.Away.before _ query 200 2701134824 (by decide) (by decide) lower)
      (CopyGeneral.Away.before _ query 136 2701134824 (by decide) (by decide) lower)
      (CopyGeneral.Away.after _ query 32 layout.ommerAligned (by have upper:=layout.ommerArena.upper; omega) before) normal).memory

theorem marked_ommer_before (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap query : BitVec 64) (layout : OmmerLayout heap) (before : query.toNat<(temporaryBase heap).toNat) :
    (markedOmmer source pointer record heap).memory query=(firstStored source pointer record heap).memory query := by
  have backing:=AllocatedBytes.aligned_number (temporaryBase heap)
  have aligned:=layout.temporaryAligned
  apply ByteStore.away
  intro same
  have number:=congrArg BitVec.toNat same
  omega

theorem OmmerHashOutput.older (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap query : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput source pointer record heap target)
    (lower : 2701134824≤query.toNat) (before : query.toNat<heap.toNat) : target.memory query=source.memory query := by
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  rw [output.memory query lower (by omega),marked_ommer_before source pointer record heap query layout (by omega)]
  exact first_stored_older source pointer record heap query layout.headerArena before

theorem OmmerHashOutput.cells (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput source pointer record heap target)
    (lower : 2701134824≤heap.toNat) (slot : Nat) (inside : slot<31) :
    target.memory (heap+BitVec.ofNat 64 (8*slot))=.word (initialHeaderWord pointer slot) := by
  have number:=byteAddress_toNat heap (8*slot) (by have upper:=layout.headerArena.upper; omega)
  change (heap+BitVec.ofNat 64 (8*slot)).toNat=heap.toNat+8*slot at number
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  rw [output.memory _ (by omega) (by omega),marked_ommer_before source pointer record heap _ layout (by omega)]
  exact first_stored_cells source pointer record heap layout.headerArena slot inside

def afterOmmerHeap (heap : BitVec 64):=PersistentAlloc.rounded (temporaryBase heap) 8#64

theorem OmmerHashOutput.heap (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (output : OmmerHashOutput source pointer record heap target) :
    target.globals.lookup (ofString "heap_ptr")=some (.val (.word (afterOmmerHeap heap))) := by
  rw [output.globals]
  simp [markedOmmer,temporaryAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,afterOmmerHeap]

/-- Main's retained real input reaches this hash's genuine returned state;
all buffer geometry and funding come from the same continuing prefix. -/
theorem ommer_hash {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ boundary+32≤heap.toNat ∧
      OmmerLayout heap ∧ OmmerHashOutput source pointer record heap hashed ∧ CallPrefix.Execution hashed afterOmmerHash current := by
  obtain ⟨heap,heapCell,headerRoom,arena,aligned,before,next⟩:=first_stores data execution
  obtain ⟨ohRoom,tmpRoom,ohArena,tmpArena,ohAligned,tmpAligned,headerBefore,ommerBefore,allocated⟩:=
    ommer_from_execution source current pointer record heap data.arena.code arena headerRoom next
  let layout : OmmerLayout heap:=⟨arena,headerRoom,aligned,ohArena,ohRoom,tmpArena,tmpRoom,ohAligned,tmpAligned,headerBefore,ommerBefore⟩
  obtain ⟨hashed,output,rest⟩:=ommer_hash_from_execution source current pointer record heap data.keccak layout allocated
  exact ⟨heap,hashed,heapCell,before,layout,output,rest⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.marked_ommer_globals
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.marked_ommer_environment
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_hash_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.marked_ommer_before
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.older
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.cells
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.OmmerHashOutput.heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_hash
