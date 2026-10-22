import InitECandidate.Solver.Input.PayloadHeaderBaseFeeReached

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

def requestsBase (heap : BitVec 64):=PersistentAlloc.rounded (withdrawalBase heap) 32#64
def afterWithdrawalAllocation : List CallPrefix.Action:=afterBaseFee.drop 1
def allocatedWithdrawal (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (baseFeeStored input source hashed heap words) (ofString "wr") (withdrawalBase heap) 32#64

set_option maxRecDepth 100000 in
theorem withdrawal_allocation_action : afterBaseFee=
    .scoped (ofString "wr") .one (ofString "alloc") [.const 32#64]::afterWithdrawalAllocation := by
  simp only [afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,
    afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,
    shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterWithdrawalAllocation]
  rfl

theorem withdrawal_allocation_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words) (installed : OriginalCode.Installed source.code)
    (frame : HeaderFrame input source heap (baseFeeStored input source hashed heap words))
    (frontier : HeapFrontier (baseFeeStored input source hashed heap words) heap (withdrawalBase heap))
    (execution : CallPrefix.Execution (baseFeeStored input source hashed heap words) afterBaseFee current) :
    AllocatedBytes.Arena (withdrawalBase heap) 32 ∧
      HeaderFrame input source heap (allocatedWithdrawal input source hashed heap words) ∧
      HeapFrontier (allocatedWithdrawal input source hashed heap words) heap (requestsBase heap) ∧
      CallPrefix.Execution (allocatedWithdrawal input source hashed heap words) afterWithdrawalAllocation current := by
  rw [withdrawal_allocation_action] at execution
  exact allocate_field input source _ current heap (withdrawalBase heap) 32#64 (ofString "wr") _ installed frame frontier
    (by decide) (by decide) (by decide) (by decide) execution

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.withdrawal_allocation_action
#print axioms InitECandidate.Solver.Input.PayloadHeader.withdrawal_allocation_from_execution
