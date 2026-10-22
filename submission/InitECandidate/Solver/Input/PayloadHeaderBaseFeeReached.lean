import InitECandidate.Solver.Input.PayloadHeaderBaseFee
import InitECandidate.Solver.Input.PayloadHeaderFrontier

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main Main.RunAttemptConstructors

def withdrawalBase (heap : BitVec 64):=PersistentAlloc.rounded (zeroBase heap) 8#64

theorem base_fee_frontier (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) (arena : AllocatedBytes.Arena (zeroBase heap) 8)
    (before : heap.toNat+248≤(zeroBase heap).toNat) :
    HeapFrontier (baseFeeStored input source hashed heap words) heap (withdrawalBase heap) := by
  have growth:=PersistentAlloc.guards (zeroBase heap) 8#64 arena.upper
  have grows:=growth.2.2.1
  change (zeroBase heap).toNat+8≤(withdrawalBase heap).toNat at grows
  constructor
  · simp [baseFeeStored,wideStored,storedField,feeEntry,zeroPointerStored,clearedZero,allocatedZero,PersistentAlloc.post,
      setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,withdrawalBase]
  · exact ⟨by have h:=arena.lower; omega,by have h:=growth.2.2.2.1; change (withdrawalBase heap).toNat≤33806089496 at h; omega⟩
  · exact growth.2.2.2.2
  · omega

/-- Actual main provenance reaches all initial scalar fields, the zero
buffer and the real four-word base-fee store, retaining old decoded/state
memory and deriving the next aligned allocation frontier. -/
theorem base_fee_reached (input : Guest.InputBlob) (origin initializer source current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,∃ words : RlpWrite.U256Value.Words,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
      workspace.toNat+40≤heap.toNat ∧ root.toNat≤heap.toNat ∧ OmmerLayout heap ∧ OmmerHashOutput input source heap hashed ∧
      AllocatedBytes.Arena (afterOmmerHeap heap) 32 ∧ AllocatedBytes.Arena (zeroBase heap) 8 ∧
      HeaderFrame input source heap (baseFeeStored input source hashed heap words) ∧
      HeapFrontier (baseFeeStored input source hashed heap words) heap (withdrawalBase heap) ∧
      CallPrefix.Execution (baseFeeStored input source hashed heap words) afterBaseFee current := by
  obtain ⟨heap,hashed,heapCell,workspaceBefore,rootBefore,layout,output,txrArena,txrAligned,txrBefore,next⟩:=
    transaction_root_allocation input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
  obtain ⟨fixedFrame,fixedTrace⟩:=before_zero_from_execution input origin source hashed current heap root counts prepared rootBefore
    layout output ready.environment.domain next
  obtain ⟨zeroArena,zeroAligned,zeroBefore,zeroFrame,zeroTrace⟩:=zero_allocation_from_execution input source hashed current heap ready.state.1 fixedFrame txrArena fixedTrace
  have headerBefore:=layout.headerBefore
  have ommerBefore:=layout.ommerBefore
  have beforeZero : heap.toNat+248≤(zeroBase heap).toNat:=by omega
  obtain ⟨clearedFrame,clearedTrace⟩:=zero_buffer_from_execution input source hashed current heap ready.state.1 ready.environment.domain
    layout zeroArena zeroAligned (by omega) zeroFrame zeroTrace
  obtain ⟨words,read,feeFrame,feeTrace⟩:=base_fee_from_execution input source hashed current heap layout ready.environment.domain clearedFrame clearedTrace
  exact ⟨heap,hashed,words,heapCell,workspaceBefore,rootBefore,layout,output,txrArena,zeroArena,feeFrame,
    base_fee_frontier input source hashed heap words zeroArena beforeZero,feeTrace⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.base_fee_frontier
#print axioms InitECandidate.Solver.Input.PayloadHeader.base_fee_reached
