import InitECandidate.Solver.Input.PayloadHeaderBeforeZero

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def zeroBase (heap : BitVec 64):=PersistentAlloc.rounded (afterOmmerHeap heap) 32#64
def afterZeroAllocation : List CallPrefix.Action:=afterBeforeZero.drop 1
def allocatedZero (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  let before:=beforeZero input source hashed heap
  setVarHOLFinite (ofString "z8") (.val (.word (zeroBase heap)))
    (PersistentAlloc.post {before with clock:=before.clock-1} (zeroBase heap) 8#64)

set_option maxRecDepth 100000 in
theorem zero_allocation_action : afterBeforeZero=
    .scoped (ofString "z8") .one (ofString "alloc") [.const 8#64]::afterZeroAllocation := by
  simp only [afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,
    afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterZeroAllocation]
  rfl

theorem before_zero_heap (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    (beforeZero input source hashed heap).globals.lookup (ofString "heap_ptr")=some (.val (.word (zeroBase heap))) := by
  simp [beforeZero,scalarPrefixStored,payloadFieldsStored,scalarFields,wideZeroStored,bloomPointerStored,receiptsPointerStored,
    transactionPointerStored,storedField,allocatedTransactionRoot,PersistentAlloc.post,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,zeroBase]

theorem zero_allocation_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (installed : OriginalCode.Installed source.code)
    (frame : HeaderFrame input source heap (beforeZero input source hashed heap))
    (transactionArena : AllocatedBytes.Arena (afterOmmerHeap heap) 32)
    (execution : CallPrefix.Execution (beforeZero input source hashed heap) afterBeforeZero current) :
    AllocatedBytes.Arena (zeroBase heap) 8 ∧ (zeroBase heap).toNat%8=0 ∧
      (afterOmmerHeap heap).toNat+32≤(zeroBase heap).toNat ∧
      HeaderFrame input source heap (allocatedZero input source hashed heap) ∧
      CallPrefix.Execution (allocatedZero input source hashed heap) afterZeroAllocation current := by
  rw [zero_allocation_action] at execution
  have growth:=PersistentAlloc.guards (afterOmmerHeap heap) 32#64 transactionArena.upper
  have actualInstalled : OriginalCode.Installed (beforeZero input source hashed heap).code:=by rw [frame.code]; exact installed
  have args : evalListHOLFinite (beforeZero input source hashed heap)
      (h:=fun address=>Classical.propDecidable ((beforeZero input source hashed heap).memaddrs address)) [.const 8#64]=some (PersistentAlloc.values 8#64):=by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,next⟩:=CallPrefix.Execution.alloc_next (source:=beforeZero input source hashed heap) (target:=current)
    (ofString "z8") [.const 8#64] (zeroBase heap) 8#64 afterZeroAllocation actualInstalled args
    (before_zero_heap input source hashed heap) growth.2.2.2.1 execution
  have previousLower:=transactionArena.lower
  have before:=growth.2.2.1
  change (afterOmmerHeap heap).toNat+32≤(zeroBase heap).toNat at before
  exact ⟨⟨by omega,room⟩,growth.2.2.2.2,before,
    frame.allocated input source _ heap (ofString "z8") _ _ (by decide) (by decide) (by decide) (by decide),next⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.zero_allocation_action
#print axioms InitECandidate.Solver.Input.PayloadHeader.before_zero_heap
#print axioms InitECandidate.Solver.Input.PayloadHeader.zero_allocation_from_execution
