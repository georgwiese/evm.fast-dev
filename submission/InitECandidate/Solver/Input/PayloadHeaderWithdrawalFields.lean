import InitECandidate.Solver.Input.PayloadHeaderWithdrawalAllocation

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def withdrawalScalarFields : List (Nat×Nat):=[(200,112),(208,120)]
def afterWithdrawalFields : List CallPrefix.Action:=afterWithdrawalAllocation.drop 4
def withdrawalPointerStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  storedField (allocatedWithdrawal input source hashed heap words) heap 192 (withdrawalBase heap)
def withdrawalScalarsStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  payloadFieldsStored input source heap (withdrawalPointerStored input source hashed heap words) withdrawalScalarFields
def beforeRequests (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  storedField (withdrawalScalarsStored input source hashed heap words) heap 216 (inputPointer+26#64)

set_option maxRecDepth 100000 in
theorem withdrawal_field_actions : afterWithdrawalAllocation=
    .command (storeField 192 (localVar "wr"))::
    (payloadFieldActions withdrawalScalarFields++
      .command (storeField 216 (RequestRootHash.fieldExpression 24))::afterWithdrawalFields) := by
  simp only [afterWithdrawalAllocation,afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,
    afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,
    Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterWithdrawalFields,payloadFieldActions,
    withdrawalScalarFields,storeField,headerAddress,PayloadHash.fieldExpression,RequestRootHash.fieldExpression,localVar,List.cons_append,List.nil_append]
  rfl

theorem withdrawal_fields_valid : ∀ field∈withdrawalScalarFields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0 := by
  intro field member
  simp only [withdrawalScalarFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> decide

theorem withdrawal_fields_from_execution (input : Guest.InputBlob) (origin source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (words : RlpWrite.U256Value.Words) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts) (rootBefore : root.toNat≤heap.toNat)
    (originalFrame : HashInput.Frame origin source inputPointer.toNat root.toNat)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (layout : OmmerLayout heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (frame : HeaderFrame input source heap (allocatedWithdrawal input source hashed heap words))
    (frontier : HeapFrontier (allocatedWithdrawal input source hashed heap words) heap (requestsBase heap))
    (execution : CallPrefix.Execution (allocatedWithdrawal input source hashed heap words) afterWithdrawalAllocation current) :
    HeaderFrame input source heap (beforeRequests input source hashed heap words) ∧
      HeapFrontier (beforeRequests input source hashed heap words) heap (requestsBase heap) ∧
      CallPrefix.Execution (beforeRequests input source hashed heap words) afterWithdrawalFields current := by
  rw [withdrawal_field_actions] at execution
  have wrCell : (allocatedWithdrawal input source hashed heap words).locals.lookup (ofString "wr")=some (.val (.word (withdrawalBase heap))):=
    bind_lookup_same _ _ _
  have first:=store_field_execute _ heap 192 (withdrawalBase heap) (localVar "wr") (frame.domain.trans domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame.header (Request.local_word _ "wr" _ wrCell)
  have trace1:=execution.command_known _ _ first
  have frame1:=frame.stored input source _ heap 192 (withdrawalBase heap) layout.headerArena (by decide)
  obtain ⟨frame2,trace2⟩:=payload_fields_from_execution input origin source heap root counts prepared rootBefore domain
    layout.headerArena layout.headerAligned withdrawalScalarFields _ withdrawal_fields_valid _ current frame1 trace1
  let data:=RequestRootHashData.description input counts
  have currentInput:=frame2.input_frame input origin source _ heap root originalFrame rootBefore
  have parentRead:=data.field_read origin (withdrawalScalarsStored input source hashed heap words) _ _ _
    prepared.image prepared.layout currentInput (frame2.domain.trans domain) (frame2.si.trans siCell)
    (24,data.parent) (by simp [RequestRootHash.Description.cells])
  have last:=store_field_execute _ heap 216 (inputPointer+26#64) (RequestRootHash.fieldExpression 24) (frame2.domain.trans domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame2.header parentRead
  have finalFrame:=frame2.stored input source _ heap 216 (inputPointer+26#64) layout.headerArena (by decide)
  exact ⟨finalFrame,frontier.of_globals _ (beforeRequests input source hashed heap words) heap _ rfl,trace2.command_known _ _ last⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.withdrawal_field_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.withdrawal_fields_valid
#print axioms InitECandidate.Solver.Input.PayloadHeader.withdrawal_fields_from_execution
