import InitECandidate.Solver.Input.PersistentNormalFrame
import InitECandidate.Solver.Rlp.ValidationArena
import InitECandidate.Solver.WitnessRadix.AllocatedBytes
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Physical frame for a genuine original decoder stage. Its real heap
can advance and its real scratch cursor can decrease. All older storage
above the incoming cursor and below the incoming heap remains untouched. -/
structure NormalFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat
  nextScratch : ∃ next,Rlp.Validation.Arena target next limit ∧ next.toNat≤cursor.toNat
  domain : target.memaddrs=source.memaddrs
  endian : target.be=source.be
  code : target.code=source.code
  globals : ∀ key,key≠ofString "heap_ptr"→key≠ofString "scratch_ptr"→target.globals.lookup key=source.globals.lookup key
  memory : ∀ query : BitVec 64,cursor.toNat≤query.toNat→query.toNat<heap.toNat→target.memory query=source.memory query

theorem NormalFrame.of_erase (source target current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : NormalFrame source current heap cursor limit) (pure : Input.LocalEffects.erase target=Input.LocalEffects.erase current) :
    NormalFrame source target heap cursor limit := by
  have memory:=Input.LocalEffects.memory_of_erase current target pure
  have domain:=congrArg PanSemStateFiniteExact.memaddrs pure
  have endian:=congrArg PanSemStateFiniteExact.be pure
  have codeEq:=congrArg PanSemStateFiniteExact.code pure
  have globals:=congrArg PanSemStateFiniteExact.globals pure
  change target.globals=current.globals at globals
  obtain ⟨next,cell,arena,aligned,grows⟩:=frame.nextHeap
  obtain ⟨cursor2,scratch,below⟩:=frame.nextScratch
  exact ⟨⟨next,by rw [globals]; exact cell,arena,aligned,grows⟩,
    ⟨cursor2,scratch.of_fields current target cursor2 limit domain globals,below⟩,
    domain.trans frame.domain,endian.trans frame.endian,codeEq.trans frame.code,
    by intro key notHeap notScratch; rw [globals]; exact frame.globals key notHeap notScratch,
    by intro query above below; rw [memory]; exact frame.memory query above below⟩

theorem NormalFrame.prefix (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap cursor limit : BitVec 64)
    (frame : NormalFrame middle target heap cursor limit)
    (domain : middle.memaddrs=source.memaddrs) (endian : middle.be=source.be) (codeEq : middle.code=source.code)
    (globals : ∀ key,middle.globals.lookup key=source.globals.lookup key)
    (above : Rlp.Validation.Above source middle cursor.toNat) : NormalFrame source target heap cursor limit :=
  ⟨frame.nextHeap,frame.nextScratch,frame.domain.trans domain,frame.endian.trans endian,frame.code.trans codeEq,
    fun key notHeap notScratch=>(frame.globals key notHeap notScratch).trans (globals key),
    fun query lower upper=>(frame.memory query lower upper).trans (above query lower)⟩

/-- Compose actual decoder stages at their real evolving heap and scratch
frontiers. The agreement band is the original incoming one, not the larger
band below a later heap that may contain newly mutated nodes. -/
theorem NormalFrame.compose (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor nextHeap nextCursor limit : BitVec 64)
    (first : NormalFrame source middle heap cursor limit) (second : NormalFrame middle target nextHeap nextCursor limit)
    (grows : heap.toNat≤nextHeap.toNat) (drops : nextCursor.toNat≤cursor.toNat) : NormalFrame source target heap cursor limit := by
  obtain ⟨heap3,cell,arena,aligned,nextGrows⟩:=second.nextHeap
  obtain ⟨cursor3,scratch,nextDrops⟩:=second.nextScratch
  exact ⟨⟨heap3,cell,arena,aligned,Nat.le_trans grows nextGrows⟩,⟨cursor3,scratch,Nat.le_trans nextDrops drops⟩,
    second.domain.trans first.domain,second.endian.trans first.endian,second.code.trans first.code,
    fun key notHeap notScratch=>(second.globals key notHeap notScratch).trans (first.globals key notHeap notScratch),
    fun query above below=>(second.memory query (Nat.le_trans drops above) (Nat.lt_of_lt_of_le below grows)).trans (first.memory query above below)⟩

/-- Frame for the current above-heap scratch layout. Both protected sides
are required: earlier persistent words and older live scratch records. -/
structure LiveFrame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) : Prop where
  nextHeap : ∃ next,target.globals.lookup (ofString "heap_ptr")=some (.val (.word next)) ∧
    AllocatedBytes.Arena next 0 ∧ next.toNat≤2952790016 ∧ next.toNat%8=0 ∧ heap.toNat≤next.toNat
  nextScratch : ∃ next,Rlp.Validation.Arena target next limit ∧ next.toNat≤cursor.toNat
  live : Rlp.LiveArena target
  metadata : Input.MemoryMetadata.erase {target with globals:=source.globals}=Input.MemoryMetadata.erase source
  globals : ∀ key,key≠ofString "heap_ptr"→key≠ofString "scratch_ptr"→target.globals.lookup key=source.globals.lookup key
  memoryBefore : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query
  memoryAbove : Rlp.Validation.Above source target cursor.toNat

/-- A real persistent-allocation frame retains its live scratch cursors.
The additional upper memory frame is derived by the actual caller. -/
theorem LiveFrame.of_persistent (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (persistent : Input.PersistentNormalFrame source target heap)
    (above : Rlp.Validation.Above source target cursor.toNat) : LiveFrame source target heap cursor limit := by
  have domain:=Input.MemoryMetadata.domain persistent.metadata
  change target.memaddrs=source.memaddrs at domain
  have codeEq:=Input.MemoryMetadata.code persistent.metadata
  change target.code=source.code at codeEq
  have scratch:=(persistent.globals (ofString "scratch_ptr") (by decide))
  have frame:=(persistent.globals (ofString "frame_mem_ptr") (by decide))
  have physical : Rlp.Validation.Arena target cursor limit:=
    ⟨domain.trans arena.domain,scratch.trans arena.cursorGlobal,frame.trans arena.limitGlobal,
      arena.ordered,arena.aligned,arena.lower,arena.upper⟩
  exact ⟨persistent.nextHeap,⟨cursor,physical,Nat.le_refl _⟩,live.of_cursors domain codeEq scratch frame,
    persistent.metadata,fun key notHeap notScratch=>persistent.globals key notHeap,persistent.memory,above⟩

/-- Actual parser prefixes keep the same heap and both live cursors. Their
precise upper frame protects older records while temporary scratch changes. -/
theorem LiveFrame.of_parser (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (bounded : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (metadata : Input.MemoryMetadata.erase target=Input.MemoryMetadata.erase source)
    (before : ∀ query : BitVec 64,query.toNat<heap.toNat→target.memory query=source.memory query)
    (above : Rlp.Validation.Above source target cursor.toNat) : LiveFrame source target heap cursor limit := by
  have globals:=congrArg PanSemStateFiniteExact.globals metadata
  change target.globals=source.globals at globals
  have runtime:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) metadata
  change Input.MemoryMetadata.erase {target with globals:=source.globals}=Input.MemoryMetadata.erase source at runtime
  have persistent : Input.PersistentNormalFrame source target heap:=
    ⟨⟨heap,by rw [globals]; exact heapCell,heapArena,bounded,aligned,Nat.le_refl _⟩,runtime,
      by intro key other; rw [globals],before⟩
  exact LiveFrame.of_persistent source target heap cursor limit live arena persistent above

/-- Compose the real growing heap and decreasing scratch frontiers. The
original protected input and record ranges remain the same throughout. -/
theorem LiveFrame.compose (source middle target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor nextHeap nextCursor limit : BitVec 64)
    (first : LiveFrame source middle heap cursor limit) (second : LiveFrame middle target nextHeap nextCursor limit)
    (grows : heap.toNat≤nextHeap.toNat) (drops : nextCursor.toNat≤cursor.toNat) : LiveFrame source target heap cursor limit := by
  obtain ⟨last,cell,allocation,bounded,aligned,later⟩:=second.nextHeap
  obtain ⟨scratch,physical,decreases⟩:=second.nextScratch
  have runtime:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) second.metadata
  change Input.MemoryMetadata.erase {target with globals:=source.globals}=Input.MemoryMetadata.erase {middle with globals:=source.globals} at runtime
  exact ⟨⟨last,cell,allocation,bounded,aligned,Nat.le_trans grows later⟩,⟨scratch,physical,Nat.le_trans decreases drops⟩,
    second.live,runtime.trans first.metadata,
    fun key notHeap notScratch=>(second.globals key notHeap notScratch).trans (first.globals key notHeap notScratch),
    fun query before=>(second.memoryBefore query (Nat.lt_of_lt_of_le before grows)).trans (first.memoryBefore query before),
    fun query above=>(second.memoryAbove query (Nat.le_trans drops above)).trans (first.memoryAbove query above)⟩

/-- Real caller entry and lexical restoration only alter erased fields. -/
theorem LiveFrame.of_erase (source target source' target' : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap cursor limit : BitVec 64) (frame : LiveFrame source target heap cursor limit)
    (entry : Input.LocalEffects.erase source'=Input.LocalEffects.erase source)
    (exit : Input.LocalEffects.erase target'=Input.LocalEffects.erase target) : LiveFrame source' target' heap cursor limit := by
  have sourceGlobals:=congrArg PanSemStateFiniteExact.globals entry
  have targetGlobals:=congrArg PanSemStateFiniteExact.globals exit
  change source'.globals=source.globals at sourceGlobals
  change target'.globals=target.globals at targetGlobals
  have sourceMemory:=Input.LocalEffects.memory_of_erase source source' entry
  have targetMemory:=Input.LocalEffects.memory_of_erase target target' exit
  have domain:=congrArg PanSemStateFiniteExact.memaddrs exit
  have runtime:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with globals:=source.globals}) (Input.MemoryMetadata.of_frame exit)
  change Input.MemoryMetadata.erase {target' with globals:=source.globals}=Input.MemoryMetadata.erase {target with globals:=source.globals} at runtime
  have metadata:=runtime.trans (frame.metadata.trans (Input.MemoryMetadata.of_frame entry).symm)
  rw [←sourceGlobals] at metadata
  obtain ⟨next,cell,allocation,bounded,aligned,grows⟩:=frame.nextHeap
  obtain ⟨scratch,physical,decreases⟩:=frame.nextScratch
  exact ⟨⟨next,by rw [targetGlobals]; exact cell,allocation,bounded,aligned,grows⟩,
    ⟨scratch,physical.of_fields target target' scratch limit domain targetGlobals,decreases⟩,
    frame.live.of_frame exit,metadata,
    by intro key notHeap notScratch; rw [sourceGlobals,targetGlobals]; exact frame.globals key notHeap notScratch,
    by intro query before; rw [sourceMemory,targetMemory]; exact frame.memoryBefore query before,
    by intro query above; rw [sourceMemory,targetMemory]; exact frame.memoryAbove query above⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.of_erase
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.prefix
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.NormalFrame.compose

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LiveFrame.of_persistent
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LiveFrame.of_parser
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LiveFrame.compose
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.LiveFrame.of_erase
