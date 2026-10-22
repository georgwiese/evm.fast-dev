import InitECandidate.Solver.Input.PayloadHeaderWithdrawalFields

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def balanceBase (heap : BitVec 64):=PersistentAlloc.rounded (requestsBase heap) 32#64
def headerFrontier (heap : BitVec 64):=PersistentAlloc.rounded (balanceBase heap) 32#64
def allocatedRequests (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (beforeRequests input source hashed heap words) (ofString "rh") (requestsBase heap) 32#64
def requestsPointerStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  storedField (allocatedRequests input source hashed heap words) heap 224 (requestsBase heap)
def allocatedBalance (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (requestsPointerStored input source hashed heap words) (ofString "bh") (balanceBase heap) 32#64
def balancePointerStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  storedField (allocatedBalance input source hashed heap words) heap 232 (balanceBase heap)
def completeHeader (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  storedField (balancePointerStored input source hashed heap words) heap 240 (inputWord input source 128)

set_option maxRecDepth 100000 in
theorem remaining_buffer_actions : afterWithdrawalFields=[
    .scoped (ofString "rh") .one (ofString "alloc") [.const 32#64],
    .command (storeField 224 (localVar "rh")),
    .scoped (ofString "bh") .one (ofString "alloc") [.const 32#64],
    .command (storeField 232 (localVar "bh")),
    .command (storeField 240 (PayloadHash.fieldExpression 128))] := by
  simp only [afterWithdrawalFields,afterWithdrawalAllocation,afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,
    afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,storeField,headerAddress,PayloadHash.fieldExpression,localVar]
  rfl

theorem remaining_buffers_from_execution (input : Guest.InputBlob) (origin source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (words : RlpWrite.U256Value.Words) (counts : Nat→BitVec 64)
    (prepared : RequestRootHashData.Prepared input origin root counts) (rootBefore : root.toNat≤heap.toNat)
    (installed : OriginalCode.Installed source.code) (layout : OmmerLayout heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (frame : HeaderFrame input source heap (beforeRequests input source hashed heap words))
    (frontier : HeapFrontier (beforeRequests input source hashed heap words) heap (requestsBase heap))
    (execution : CallPrefix.Execution (beforeRequests input source hashed heap words) afterWithdrawalFields current) :
    AllocatedBytes.Arena (requestsBase heap) 32 ∧ AllocatedBytes.Arena (balanceBase heap) 32 ∧
      HeaderFrame input source heap (completeHeader input source hashed heap words) ∧
      HeapFrontier (completeHeader input source hashed heap words) heap (headerFrontier heap) ∧
      current=completeHeader input source hashed heap words := by
  rw [remaining_buffer_actions] at execution
  obtain ⟨requestArena,frame1,frontier1,trace1⟩:=allocate_field input source _ current heap (requestsBase heap) 32#64 (ofString "rh") _
    installed frame frontier (by decide) (by decide) (by decide) (by decide) execution
  have rhCell : (allocatedRequests input source hashed heap words).locals.lookup (ofString "rh")=some (.val (.word (requestsBase heap))):=
    bind_lookup_same _ _ _
  have storeRh:=store_field_execute _ heap 224 (requestsBase heap) (localVar "rh") (frame1.domain.trans domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame1.header (Request.local_word _ "rh" _ rhCell)
  have trace2:=trace1.command_known _ _ storeRh
  have frame2:=frame1.stored input source _ heap 224 (requestsBase heap) layout.headerArena (by decide)
  have frontier2:=frontier1.of_globals _ (requestsPointerStored input source hashed heap words) heap (balanceBase heap) rfl
  obtain ⟨balanceArena,frame3,frontier3,trace3⟩:=allocate_field input source _ current heap (balanceBase heap) 32#64 (ofString "bh") _
    installed frame2 frontier2 (by decide) (by decide) (by decide) (by decide) trace2
  have bhCell : (allocatedBalance input source hashed heap words).locals.lookup (ofString "bh")=some (.val (.word (balanceBase heap))):=
    bind_lookup_same _ _ _
  have storeBh:=store_field_execute _ heap 232 (balanceBase heap) (localVar "bh") (frame3.domain.trans domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame3.header (Request.local_word _ "bh" _ bhCell)
  have trace4:=trace3.command_known _ _ storeBh
  have frame4:=frame3.stored input source _ heap 232 (balanceBase heap) layout.headerArena (by decide)
  have readValue:=frame4.payload_read input origin source _ heap root counts prepared rootBefore domain 128 (by decide) (by decide)
  have last:=store_field_execute _ heap 240 (inputWord input source 128) (PayloadHash.fieldExpression 128) (frame4.domain.trans domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame4.header readValue
  have trace5:=trace4.command_known _ _ last
  have frame5:=frame4.stored input source _ heap 240 (inputWord input source 128) layout.headerArena (by decide)
  have same : current=completeHeader input source hashed heap words:=by cases trace5; rfl
  exact ⟨requestArena,balanceArena,frame5,frontier3.of_globals _ (completeHeader input source hashed heap words) heap (headerFrontier heap) rfl,same⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.remaining_buffer_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.remaining_buffers_from_execution
