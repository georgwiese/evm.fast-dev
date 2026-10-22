import InitECandidate.Solver.Input.PayloadHeaderFirstStores

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def ommerBase (heap : BitVec 64):=PersistentAlloc.rounded heap 248#64
def temporaryBase (heap : BitVec 64):=PersistentAlloc.rounded (ommerBase heap) 32#64
def afterOmmerBuffers : List CallPrefix.Action:=afterFirstStores.drop 2
def ommerAllocated (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let before:=parentStoredHeader input source heap
  setVarHOLFinite (ofString "oh") (.val (.word (ommerBase heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (ommerBase heap) 32#64)
def temporaryAllocated (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let before:=ommerAllocated input source heap
  setVarHOLFinite (ofString "tmp") (.val (.word (temporaryBase heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (temporaryBase heap) 8#64)

set_option maxRecDepth 100000 in
theorem ommer_buffer_actions : afterFirstStores=
    .scoped (ofString "oh") .one (ofString "alloc") [.const 32#64]::
    .scoped (ofString "tmp") .one (ofString "alloc") [.const 8#64]::afterOmmerBuffers := by
  simp only [afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterOmmerBuffers]
  rfl

theorem parent_heap (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (parentStoredHeader input source heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (ommerBase heap))) := by
  simp [parentStoredHeader,markedHeader,clearedHeader,allocatedHeader,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,ommerBase]

theorem ommer_heap (input : Guest.InputBlob) (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (ommerAllocated input source heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (temporaryBase heap))) := by
  simp [ommerAllocated,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,temporaryBase]

/-- Both ommer buffers are fresh regions derived from the two actual
normal allocations, with their true caller states and monotone frontiers. -/
theorem ommer_from_execution (input : Guest.InputBlob) (source current : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (installed : OriginalCode.Installed source.code) (headerArena : AllocatedBytes.Arena heap 248)
    (execution : CallPrefix.Execution (parentStoredHeader input source heap) afterFirstStores current) :
    AllocatedBytes.Arena (ommerBase heap) 32 ∧ AllocatedBytes.Arena (temporaryBase heap) 8 ∧
      (ommerBase heap).toNat%8=0 ∧ (temporaryBase heap).toNat%8=0 ∧
      heap.toNat+248≤(ommerBase heap).toNat ∧ (ommerBase heap).toNat+32≤(temporaryBase heap).toNat ∧
      CallPrefix.Execution (temporaryAllocated input source heap) afterOmmerBuffers current := by
  rw [ommer_buffer_actions] at execution
  have headerGrowth:=PersistentAlloc.guards heap 248#64 headerArena.upper
  have argsOH : evalListHOLFinite (parentStoredHeader input source heap)
      (h:=fun address=>Classical.propDecidable ((parentStoredHeader input source heap).memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨ommerRoom,afterOmmer⟩:=CallPrefix.Execution.alloc_next (source:=parentStoredHeader input source heap) (target:=current)
    (ofString "oh") [.const 32#64] (ommerBase heap) 32#64 _ installed argsOH (parent_heap input source heap) headerGrowth.2.2.2.1 execution
  have ommerGrowth:=PersistentAlloc.guards (ommerBase heap) 32#64 ommerRoom
  have argsTmp : evalListHOLFinite (ommerAllocated input source heap)
      (h:=fun address=>Classical.propDecidable ((ommerAllocated input source heap).memaddrs address)) [.const 8#64]=some (PersistentAlloc.values 8#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨temporaryRoom,afterTemporary⟩:=CallPrefix.Execution.alloc_next (source:=ommerAllocated input source heap) (target:=current)
    (ofString "tmp") [.const 8#64] (temporaryBase heap) 8#64 afterOmmerBuffers installed argsTmp (ommer_heap input source heap) ommerGrowth.2.2.2.1 afterOmmer
  have headerLower:=headerArena.lower
  have afterHeader:=headerGrowth.2.2.1
  have afterOmmer:=ommerGrowth.2.2.1
  change heap.toNat+248≤(ommerBase heap).toNat at afterHeader
  change (ommerBase heap).toNat+32≤(temporaryBase heap).toNat at afterOmmer
  refine ⟨⟨by change 2701131776≤(ommerBase heap).toNat; omega,ommerRoom⟩,
    ⟨by change 2701131776≤(temporaryBase heap).toNat; omega,temporaryRoom⟩,
    headerGrowth.2.2.2.2,ommerGrowth.2.2.2.2,afterHeader,afterOmmer,afterTemporary⟩

theorem ommer_allocations (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap,source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      AllocatedBytes.Arena heap 248 ∧ heap.toNat%8=0 ∧ workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧
      AllocatedBytes.Arena (ommerBase heap) 32 ∧ AllocatedBytes.Arena (temporaryBase heap) 8 ∧
      (ommerBase heap).toNat%8=0 ∧ (temporaryBase heap).toNat%8=0 ∧
      heap.toNat+248≤(ommerBase heap).toNat ∧ (ommerBase heap).toNat+32≤(temporaryBase heap).toNat ∧
      CallPrefix.Execution (temporaryAllocated input source heap) afterOmmerBuffers current := by
  obtain ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,next⟩:=first_stores input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  exact ⟨heap,heapCell,arena,aligned,workspaceBefore,rootBefore,ommer_from_execution input source current heap ready.state.1 arena next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_buffer_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.parent_heap
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_heap
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.ommer_allocations
