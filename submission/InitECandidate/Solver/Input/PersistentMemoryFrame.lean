import InitECandidate.Solver.Input.PersistentNormalFrame
import InitECandidate.Solver.Input.GlobalAssignNormal
import InitECandidate.Solver.Input.WordStoreNormal

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Persistent stages may initialize their own globals while retaining
an actual bounded/aligned heap, full runtime metadata and earlier memory.
Specific unchanged globals are supplied by the separate checked effect frame. -/
structure PersistentMemoryFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat≤2952790016 ∧ next.toNat%8=0 ∧ frontier.toNat≤next.toNat
  metadata : MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source
  memory : ∀ query : BitVec 64,query.toNat<frontier.toNat→target.memory query=source.memory query

theorem PersistentNormalFrame.memory_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {heap : BitVec 64}
    (frame : PersistentNormalFrame source target heap) : PersistentMemoryFrame source target heap:=⟨frame.nextHeap,frame.metadata,frame.memory⟩

theorem PersistentMemoryFrame.weaken (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier lower : BitVec 64) (frame : PersistentMemoryFrame source target frontier) (before : lower.toNat≤frontier.toNat) :
    PersistentMemoryFrame source target lower := by
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  exact ⟨⟨next,cell,arena,bounded,aligned,Nat.le_trans before grows⟩,frame.metadata,
    fun query earlier=>frame.memory query (Nat.lt_of_lt_of_le earlier before)⟩

theorem PersistentMemoryFrame.trans (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier next : BitVec 64) (first : PersistentMemoryFrame source middle frontier)
    (second : PersistentMemoryFrame middle target next) (grows : frontier.toNat≤next.toNat) :
    PersistentMemoryFrame source target frontier := by
  obtain ⟨last,cell,arena,bounded,aligned,later⟩:=second.nextHeap
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) second.metadata
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase {middle with globals:=source.globals} at metadata
  exact ⟨⟨last,cell,arena,bounded,aligned,Nat.le_trans grows later⟩,metadata.trans first.metadata,
    fun query before=>(second.memory query (Nat.lt_of_lt_of_le before grows)).trans (first.memory query before)⟩

theorem PersistentMemoryFrame.of_erase (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : BitVec 64) (frame : PersistentMemoryFrame source target frontier)
    (entry : LocalEffects.erase source'=LocalEffects.erase source)
    (exit : LocalEffects.erase target'=LocalEffects.erase target) : PersistentMemoryFrame source' target' frontier := by
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
  exact ⟨⟨next,by rw [targetGlobals]; exact cell,arena,bounded,aligned,grows⟩,total,
    by intro query before; rw [targetMemory,sourceMemory]; exact frame.memory query before⟩

/-- Initializing another global cannot change the genuine heap or runtime
and has no memory effect. The caller supplies the actual normal update. -/
theorem PersistentMemoryFrame.put_global (source middle : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : BitVec 64) (frame : PersistentMemoryFrame source middle frontier) (name : String) (word : BitVec 64)
    (other : ofString "heap_ptr"≠ofString name) : PersistentMemoryFrame source (putGlobal middle name word) frontier := by
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  exact ⟨⟨next,(putGlobal.lookup_other middle name word _ other).trans cell,arena,bounded,aligned,grows⟩,frame.metadata,frame.memory⟩

/-- A real normal word store at/after the protected frontier retains that
frame; mapping, scalar value and exact write come from the observed run. -/
theorem PersistentMemoryFrame.store_after (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : BitVec 64) (frame : PersistentMemoryFrame source middle frontier)
    (destination expression : Flapjack.Pancake.PanLang.ExpHOL 64) (address word : BitVec 64)
    (addressRead : WitnessRadix.QueryBranch.eval middle destination=some (.val (.word address)))
    (wordRead : WitnessRadix.QueryBranch.eval middle expression=some (.val (.word word)))
    (fresh : frontier.toNat≤address.toNat)
    (normal : evaluateHOLFiniteState middle (.store destination expression)=(none,target)) : PersistentMemoryFrame source target frontier := by
  obtain ⟨mapped,endpoint⟩:=word_store_normal middle target destination expression address word addressRead wordRead normal
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  refine ⟨⟨next,by rw [endpoint]; exact cell,arena,bounded,aligned,grows⟩,?_,?_⟩
  · rw [endpoint]; exact frame.metadata
  · intro query before
    rw [endpoint]
    have away : query≠address:=by intro same; subst query; omega
    exact (if_neg away).trans (frame.memory query before)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.PersistentNormalFrame.memory_frame
#print axioms InitECandidate.Solver.Input.PersistentMemoryFrame.weaken
#print axioms InitECandidate.Solver.Input.PersistentMemoryFrame.trans
#print axioms InitECandidate.Solver.Input.PersistentMemoryFrame.of_erase
#print axioms InitECandidate.Solver.Input.PersistentMemoryFrame.put_global
#print axioms InitECandidate.Solver.Input.PersistentMemoryFrame.store_after
