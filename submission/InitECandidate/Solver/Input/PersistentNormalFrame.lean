import InitECandidate.Solver.Input.MemoryMetadata
import InitECandidate.Solver.Input.CurrentStartup.ArenaFrame
import InitECandidate.Solver.WitnessRadix.AllocatedBytes

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine normal persistent-allocation stage advances the bounded heap,
retains all other globals/runtime metadata and protects all earlier words.
Scratch-frame error paths need not satisfy this normal-return contract. -/
structure PersistentNormalFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat≤2952790016 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat
  metadata : MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source
  globals : ∀ key,key≠ofString "heap_ptr"→target.globals.lookup key=source.globals.lookup key
  memory : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query

theorem PersistentNormalFrame.refl (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0) :
    PersistentNormalFrame source source heap :=
  ⟨⟨heap,heapCell,arena,bounded,aligned,Nat.le_refl _⟩,rfl,by intros; rfl,by intros; rfl⟩

theorem PersistentNormalFrame.current_arena {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    (frame : PersistentNormalFrame source target heap) (arena : CurrentStartup.ArenaState source) : CurrentStartup.ArenaState target :=
  ⟨(frame.globals _ (by decide)).trans arena.scratch,(frame.globals _ (by decide)).trans arena.frame,
    (MemoryMetadata.domain frame.metadata).trans arena.domain,by rw [MemoryMetadata.code frame.metadata]; exact arena.code⟩

/-- Compose at the actual intermediate allocator frontier. The protected
memory interval remains the earlier incoming one. -/
theorem PersistentNormalFrame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap next : BitVec 64) (first : PersistentNormalFrame source middle heap)
    (second : PersistentNormalFrame middle target next) (grows : heap.toNat≤next.toNat) :
    PersistentNormalFrame source target heap := by
  obtain ⟨last,cell,arena,bounded,aligned,later⟩:=second.nextHeap
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) second.metadata
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase {middle with globals:=source.globals} at metadata
  exact ⟨⟨last,cell,arena,bounded,aligned,Nat.le_trans grows later⟩,metadata.trans first.metadata,
    fun key other=>(second.globals key other).trans (first.globals key other),
    fun query before=>(second.memory query (Nat.lt_of_lt_of_le before grows)).trans (first.memory query before)⟩

/-- Actual call entry, restored caller locals and lexical restoration
retain the same physical allocation frame. -/
theorem PersistentNormalFrame.of_erase (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (frame : PersistentNormalFrame source target heap)
    (entry : LocalEffects.erase source'=LocalEffects.erase source)
    (exit : LocalEffects.erase target'=LocalEffects.erase target) : PersistentNormalFrame source' target' heap := by
  have sourceGlobals:=congrArg PanSemStateFiniteExact.globals entry
  have targetGlobals:=congrArg PanSemStateFiniteExact.globals exit
  change source'.globals=source.globals at sourceGlobals
  change target'.globals=target.globals at targetGlobals
  have sourceMemory:=LocalEffects.memory_of_erase source source' entry
  have targetMemory:=LocalEffects.memory_of_erase target target' exit
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) (MemoryMetadata.of_frame exit)
  change MemoryMetadata.erase {target' with globals:=source.globals}=MemoryMetadata.erase {target with globals:=source.globals} at metadata
  have total:=metadata.trans (frame.metadata.trans (MemoryMetadata.of_frame entry).symm)
  rw [←sourceGlobals] at total
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  refine ⟨⟨next,by rw [targetGlobals]; exact cell,arena,bounded,aligned,grows⟩,total,?_,?_⟩
  · intro key other
    rw [targetGlobals,sourceGlobals]
    exact frame.globals key other
  · intro query before
    rw [targetMemory,sourceMemory]
    exact frame.memory query before

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.refl
#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.current_arena
#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.trans
#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.of_erase
