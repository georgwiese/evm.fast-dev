import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderStores
import InitECandidate.Solver.WitnessRadix.ByteStoreWord

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def ommerBase (heap : BitVec 64):=PersistentAlloc.rounded heap 248#64
def temporaryBase (heap : BitVec 64):=PersistentAlloc.rounded (ommerBase heap) 32#64
def afterOmmerBuffers : List CallPrefix.Action:=afterFirstStores.drop 2
def ommerAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  let before:=firstStored source pointer record heap
  setVarHOLFinite (ofString "oh") (.val (.word (ommerBase heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (ommerBase heap) 32#64)
def temporaryAllocated (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  let before:=ommerAllocated source pointer record heap
  setVarHOLFinite (ofString "tmp") (.val (.word (temporaryBase heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (temporaryBase heap) 8#64)

set_option maxRecDepth 100000 in
theorem ommer_buffer_actions : afterFirstStores=
    .scoped (ofString "oh") .one (ofString "alloc") [.const 32#64]::
    .scoped (ofString "tmp") .one (ofString "alloc") [.const 8#64]::afterOmmerBuffers := by
  simp only [afterFirstStores,afterClear,afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterOmmerBuffers]
  rfl

theorem parent_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) :
    (firstStored source pointer record heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (ommerBase heap))) := by
  simp [firstStored,putHeader,clearedHeader,headerEntry,QueryBranch.bind,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ommerBase]

theorem ommer_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) :
    (ommerAllocated source pointer record heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (temporaryBase heap))) := by
  simp [ommerAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,temporaryBase]

/-- Both ommer buffers are fresh regions derived from the two actual
normal allocations, with their true caller states and monotone frontiers. -/
theorem ommer_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (headerArena : AllocatedBytes.Arena heap 248) (headerRoom : heap.toNat+248≤2952790016)
    (execution : CallPrefix.Execution (firstStored source pointer record heap) afterFirstStores current) :
    (ommerBase heap).toNat+32≤2952790016 ∧ (temporaryBase heap).toNat+8≤2952790016 ∧
      AllocatedBytes.Arena (ommerBase heap) 32 ∧ AllocatedBytes.Arena (temporaryBase heap) 8 ∧
      (ommerBase heap).toNat%8=0 ∧ (temporaryBase heap).toNat%8=0 ∧
      heap.toNat+248≤(ommerBase heap).toNat ∧ (ommerBase heap).toNat+32≤(temporaryBase heap).toNat ∧
      CallPrefix.Execution (temporaryAllocated source pointer record heap) afterOmmerBuffers current := by
  rw [ommer_buffer_actions] at execution
  have headerGrowth:=PersistentAlloc.guards heap 248#64 headerRoom
  have argsOH : evalListHOLFinite (firstStored source pointer record heap)
      (h:=fun address=>Classical.propDecidable ((firstStored source pointer record heap).memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨ommerRoom,afterOmmer⟩:=CallPrefix.Execution.alloc_next (source:=firstStored source pointer record heap) (target:=current)
    (ofString "oh") [.const 32#64] (ommerBase heap) 32#64 _ installed argsOH (parent_heap source pointer record heap) headerGrowth.2.2.2.1 execution
  have ommerGrowth:=PersistentAlloc.guards (ommerBase heap) 32#64 ommerRoom
  have argsTmp : evalListHOLFinite (ommerAllocated source pointer record heap)
      (h:=fun address=>Classical.propDecidable ((ommerAllocated source pointer record heap).memaddrs address)) [.const 8#64]=some (PersistentAlloc.values 8#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨temporaryRoom,afterTemporary⟩:=CallPrefix.Execution.alloc_next (source:=ommerAllocated source pointer record heap) (target:=current)
    (ofString "tmp") [.const 8#64] (temporaryBase heap) 8#64 afterOmmerBuffers installed argsTmp (ommer_heap source pointer record heap) ommerGrowth.2.2.2.1 afterOmmer
  have headerLower:=headerArena.lower
  have afterHeader:=headerGrowth.2.2.1
  have afterOmmer:=ommerGrowth.2.2.1
  change heap.toNat+248≤(ommerBase heap).toNat at afterHeader
  change (ommerBase heap).toNat+32≤(temporaryBase heap).toNat at afterOmmer
  refine ⟨ommerRoom,temporaryRoom,⟨by change 2701131776≤(ommerBase heap).toNat; omega,by omega⟩,
    ⟨by change 2701131776≤(temporaryBase heap).toNat; omega,by omega⟩,
    headerGrowth.2.2.2.2,ommerGrowth.2.2.2.2,afterHeader,afterOmmer,afterTemporary⟩

def markOmmer : ProgHOL 64:=.storeByte (localVar "tmp") (.const 192#64)
def hashOmmer : ProgHOL 64:=.call (some (none,none)) (ofString "keccak256")
  [localVar "tmp",.const 1#64,localVar "oh"]
def afterOmmerMarker : List CallPrefix.Action:=afterOmmerBuffers.drop 1
def afterOmmerHash : List CallPrefix.Action:=afterOmmerMarker.drop 1
def markedOmmer (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64):=
  let allocated:=temporaryAllocated source pointer record heap
  {allocated with memory:=ByteStore.put allocated.memory allocated.be (temporaryBase heap) 192#8}

set_option maxRecDepth 100000 in
theorem ommer_hash_actions : afterOmmerBuffers=.command markOmmer::.command hashOmmer::afterOmmerHash := by
  simp only [afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterOmmerHash,afterOmmerMarker,markOmmer,hashOmmer,localVar]
  rfl

theorem temporary_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) :
    (temporaryAllocated source pointer record heap).locals.lookup (ofString "tmp")=some (.val (.word (temporaryBase heap))) :=
  bind_lookup_same _ _ _

theorem ommer_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64) :
    (temporaryAllocated source pointer record heap).locals.lookup (ofString "oh")=some (.val (.word (ommerBase heap))) := by
  simp [temporaryAllocated,ommerAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,
    show ofString "tmp"≠ofString "oh" from by decide]

theorem ommer_marker_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena (temporaryBase heap) 8) :
    evaluateHOLFiniteState (temporaryAllocated source pointer record heap) markOmmer=(none,markedOmmer source pointer record heap) := by
  let allocated:=temporaryAllocated source pointer record heap
  have address : eval allocated (localVar "tmp")=some (.val (.word (temporaryBase heap))):=
    by
      have cell : allocated.locals.lookup (ofString "tmp")=some (.val (.word (temporaryBase heap))):=temporary_local source pointer record heap
      simp [eval,evalHOLExact,toExact,localVar,cell]
  have mapped : allocated.memaddrs (panByteAlignHOL (width:=64) (temporaryBase heap)):=by
    simpa [byteAddress] using AllocatedBytes.byte_mapped allocated (temporaryBase heap) 8 0 domain arena (by decide)
  exact ByteStore.execute_word allocated (localVar "tmp") (.const 192#64) (temporaryBase heap) 192#64 address rfl mapped

theorem ommer_marker_from_execution (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer record heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena (temporaryBase heap) 8)
    (execution : CallPrefix.Execution (temporaryAllocated source pointer record heap) afterOmmerBuffers current) :
    CallPrefix.Execution (markedOmmer source pointer record heap) (.command hashOmmer::afterOmmerHash) current := by
  rw [ommer_hash_actions] at execution
  exact execution.command_known markOmmer _ (ommer_marker_execute source pointer record heap domain arena)

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_buffer_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.parent_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_heap
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_from_execution

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_hash_actions

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.temporary_local

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_local

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_marker_execute

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.ommer_marker_from_execution
