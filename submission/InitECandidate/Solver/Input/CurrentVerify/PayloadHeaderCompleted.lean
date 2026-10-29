import InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderBaseFee

namespace InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

def requestsBase (heap : BitVec 64):=PersistentAlloc.rounded (withdrawalBase heap) 32#64
def afterWithdrawalAllocation : List CallPrefix.Action:=afterBaseFee.drop 1
def allocatedWithdrawal (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (baseFeeStored source hashed pointer record heap words) (ofString "wr") (withdrawalBase heap) 32#64

def withdrawalScalarFields : List (Nat×Nat):=[(200,112),(208,120)]
def afterWithdrawalFields : List CallPrefix.Action:=afterWithdrawalAllocation.drop 4
def withdrawalPointerStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  putHeader (allocatedWithdrawal source hashed pointer record heap words) heap 192 (withdrawalBase heap)
def withdrawalScalarsStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  payloadFieldsStored source record heap (withdrawalPointerStored source hashed pointer record heap words) withdrawalScalarFields
def beforeRequests (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  putHeader (withdrawalScalarsStored source hashed pointer record heap words) heap 216 (pointer+26#64)
def siField (offset : Nat) : ExpHOL 64:=.load .one (Scalar.plus (localVar "si") offset)

set_option maxRecDepth 100000 in
theorem withdrawal_allocation_action : afterBaseFee=
    .scoped (ofString "wr") .one (ofString "alloc") [.const 32#64]::afterWithdrawalAllocation := by
  simp only [afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,
    afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterWithdrawalAllocation]
  rfl

set_option maxRecDepth 100000 in
theorem withdrawal_field_actions : afterWithdrawalAllocation=
    .command (storeField 192 (localVar "wr"))::
    (payloadFieldActions withdrawalScalarFields++
      .command (storeField 216 (siField 24))::afterWithdrawalFields) := by
  simp only [afterWithdrawalAllocation,afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,
    afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterWithdrawalFields,payloadFieldActions,
    withdrawalScalarFields,storeField,headerField,payloadField,siField,Scalar.plus,localVar,List.cons_append,List.nil_append]
  rfl

theorem withdrawal_fields_valid : ∀ field∈withdrawalScalarFields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0 := by
  intro field member
  simp only [withdrawalScalarFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl <;> decide

/-- The earlier parent-root cell is the one written by the real decoder;
its SI record remains mapped and before the fresh header. -/
theorem HeaderFrame.parent_read {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat)
    (frame : HeaderFrame source current pointer record heap) : eval current (siField 24)=some (.val (.word (pointer+26#64))) := by
  obtain ⟨nodes,codes,headers,nodeStart,nodeLength,codeStart,codeLength,headerStart,headerLength,nodeImage,codeImage,headerImage⟩:=data.witnesses
  have number : (si+24#64).toNat=si.toNat+24:=byteAddress_toNat si 24 (by have upper:=data.siArena.upper; omega)
  have same:=frame.older (si+24#64)
    (by rw [number]; have lower:=nodeImage.siLower; omega)
    (by rw [number]; have afterSI:=nodeImage.siBefore; omega)
  have siRead:=local_word_read current "si" si (frame.si.trans data.siLocal)
  exact Witness.load_word_read current (Scalar.plus (localVar "si") 24) (si+24#64) (pointer+26#64)
    (Scalar.plus_read current (localVar "si") si 24 siRead)
    (AllocatedBytes.word_mapped current si 96 24 (frame.domain.trans data.arena.domain) data.siArena (by decide) data.siAligned (by decide))
    (same.trans data.parentCell)

theorem withdrawal_fields_from_execution {input : Guest.InputBlob} {source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat} (words : RlpWrite.U256Value.Words)
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat) (layout : OmmerLayout heap)
    (frame : HeaderFrame source (allocatedWithdrawal source hashed pointer record heap words) pointer record heap)
    (frontier : HeapFrontier (allocatedWithdrawal source hashed pointer record heap words) heap (requestsBase heap))
    (execution : CallPrefix.Execution (allocatedWithdrawal source hashed pointer record heap words) afterWithdrawalAllocation current) :
    HeaderFrame source (beforeRequests source hashed pointer record heap words) pointer record heap ∧
      HeapFrontier (beforeRequests source hashed pointer record heap words) heap (requestsBase heap) ∧
      CallPrefix.Execution (beforeRequests source hashed pointer record heap words) afterWithdrawalFields current := by
  rw [withdrawal_field_actions] at execution
  have wrCell : (allocatedWithdrawal source hashed pointer record heap words).locals.lookup (ofString "wr")=some (.val (.word (withdrawalBase heap))):=
    bind_lookup_same _ _ _
  have first:=store_field_execute _ heap 192 (withdrawalBase heap) (localVar "wr") (frame.domain.trans data.arena.domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame.header (local_word_read _ "wr" _ wrCell)
  have trace1:=execution.command_known _ _ first
  have frame1:=frame.stored source _ pointer record heap 192 (withdrawalBase heap) layout.headerArena (by decide)
  obtain ⟨frame2,trace2⟩:=payload_fields_from_execution data before layout.headerArena layout.headerAligned withdrawalScalarFields _ withdrawal_fields_valid frame1 trace1
  have last:=store_field_execute _ heap 216 (pointer+26#64) (siField 24) (frame2.domain.trans data.arena.domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame2.header (frame2.parent_read data before)
  have finalFrame:=frame2.stored source _ pointer record heap 216 (pointer+26#64) layout.headerArena (by decide)
  exact ⟨finalFrame,frontier.of_globals _ (beforeRequests source hashed pointer record heap words) heap _ rfl,trace2.command_known _ _ last⟩

def balanceBase (heap : BitVec 64):=PersistentAlloc.rounded (requestsBase heap) 32#64
def headerFrontier (heap : BitVec 64):=PersistentAlloc.rounded (balanceBase heap) 32#64
def allocatedRequests (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (beforeRequests source hashed pointer record heap words) (ofString "rh") (requestsBase heap) 32#64
def requestsPointerStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  putHeader (allocatedRequests source hashed pointer record heap words) heap 224 (requestsBase heap)
def allocatedBalance (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  allocatedField (requestsPointerStored source hashed pointer record heap words) (ofString "bh") (balanceBase heap) 32#64
def balancePointerStored (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  putHeader (allocatedBalance source hashed pointer record heap words) heap 232 (balanceBase heap)
def completeHeader (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer record heap : BitVec 64) (words : RlpWrite.U256Value.Words):=
  putHeader (balancePointerStored source hashed pointer record heap words) heap 240 (inputWord source record 128)

set_option maxRecDepth 100000 in
theorem remaining_buffer_actions : afterWithdrawalFields=[
    .scoped (ofString "rh") .one (ofString "alloc") [.const 32#64],
    .command (storeField 224 (localVar "rh")),
    .scoped (ofString "bh") .one (ofString "alloc") [.const 32#64],
    .command (storeField 232 (localVar "bh")),
    .command (storeField 240 (payloadField 128))] := by
  simp only [afterWithdrawalFields,afterWithdrawalAllocation,afterBaseFee,afterZeroBuffer,afterZeroAllocation,afterBeforeZero,
    afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,
    actions,PayloadHeader.actions,PayloadHeader.parts,PayloadHeader.body,Guest.Software.guestFn_payload_header,
    progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,storeField,headerField,payloadField,Scalar.plus,localVar]
  rfl

theorem remaining_buffers_from_execution {input : Guest.InputBlob} {source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord heap : BitVec 64} {boundary : Nat} (words : RlpWrite.U256Value.Words)
    (data : Data input source pointer si record gasWord boundary) (before : boundary≤heap.toNat) (layout : OmmerLayout heap)
    (frame : HeaderFrame source (beforeRequests source hashed pointer record heap words) pointer record heap)
    (frontier : HeapFrontier (beforeRequests source hashed pointer record heap words) heap (requestsBase heap))
    (execution : CallPrefix.Execution (beforeRequests source hashed pointer record heap words) afterWithdrawalFields current) :
    AllocatedBytes.Arena (requestsBase heap) 32 ∧ AllocatedBytes.Arena (balanceBase heap) 32 ∧
      HeaderFrame source (completeHeader source hashed pointer record heap words) pointer record heap ∧
      HeapFrontier (completeHeader source hashed pointer record heap words) heap (headerFrontier heap) ∧
      current=completeHeader source hashed pointer record heap words := by
  rw [remaining_buffer_actions] at execution
  obtain ⟨requestArena,frame1,frontier1,trace1⟩:=allocate_field source _ current pointer record heap (requestsBase heap) 32#64 (ofString "rh") _
    data.arena.code frame frontier (by decide) (by decide) (by decide) (by decide) execution
  have rhCell : (allocatedRequests source hashed pointer record heap words).locals.lookup (ofString "rh")=some (.val (.word (requestsBase heap))):=
    bind_lookup_same _ _ _
  have storeRh:=store_field_execute _ heap 224 (requestsBase heap) (localVar "rh") (frame1.domain.trans data.arena.domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame1.header (local_word_read _ "rh" _ rhCell)
  have trace2:=trace1.command_known _ _ storeRh
  have frame2:=frame1.stored source _ pointer record heap 224 (requestsBase heap) layout.headerArena (by decide)
  have frontier2:=frontier1.of_globals _ (requestsPointerStored source hashed pointer record heap words) heap (balanceBase heap) rfl
  obtain ⟨balanceArena,frame3,frontier3,trace3⟩:=allocate_field source _ current pointer record heap (balanceBase heap) 32#64 (ofString "bh") _
    data.arena.code frame2 frontier2 (by decide) (by decide) (by decide) (by decide) trace2
  have bhCell : (allocatedBalance source hashed pointer record heap words).locals.lookup (ofString "bh")=some (.val (.word (balanceBase heap))):=
    bind_lookup_same _ _ _
  have storeBh:=store_field_execute _ heap 232 (balanceBase heap) (localVar "bh") (frame3.domain.trans data.arena.domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame3.header (local_word_read _ "bh" _ bhCell)
  have trace4:=trace3.command_known _ _ storeBh
  have frame4:=frame3.stored source _ pointer record heap 232 (balanceBase heap) layout.headerArena (by decide)
  have last:=store_field_execute _ heap 240 (inputWord source record 128) (payloadField 128) (frame4.domain.trans data.arena.domain)
    layout.headerArena layout.headerAligned (by decide) (by decide) frame4.header (frame4.payload_read data before 128 (by decide) (by decide))
  have trace5:=trace4.command_known _ _ last
  have frame5:=frame4.stored source _ pointer record heap 240 (inputWord source record 128) layout.headerArena (by decide)
  have same : current=completeHeader source hashed pointer record heap words:=by cases trace5; rfl
  exact ⟨requestArena,balanceArena,frame5,frontier3.of_globals _ (completeHeader source hashed pointer record heap words) heap (headerFrontier heap) rfl,same⟩

structure HeaderBuffers (heap : BitVec 64) : Prop where
  ommer : OmmerLayout heap
  transactions : AllocatedBytes.Arena (afterOmmerHeap heap) 32
  nonce : AllocatedBytes.Arena (zeroBase heap) 8
  withdrawals : AllocatedBytes.Arena (withdrawalBase heap) 32
  requests : AllocatedBytes.Arena (requestsBase heap) 32
  balance : AllocatedBytes.Arena (balanceBase heap) 32

/-- The same real main-derived prefix supplies every header field, all
seven auxiliary buffers and the genuine block_rlp_length caller state. -/
theorem complete_header_from_execution {input : Guest.InputBlob} {source current : PanSemStateFiniteExact 64 Guest.HostMemory}
    {pointer si record gasWord : BitVec 64} {boundary : Nat}
    (data : Data input source pointer si record gasWord boundary) (execution : CallPrefix.Execution source actions current) :
    ∃ heap hashed,∃ words : RlpWrite.U256Value.Words,
      source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧ boundary+32≤heap.toNat ∧
      HeaderBuffers heap ∧ OmmerHashOutput source pointer record heap hashed ∧ HeaderFrame source current pointer record heap ∧
      HeapFrontier current heap (headerFrontier heap) ∧ current=completeHeader source hashed pointer record heap words := by
  obtain ⟨heap,hashed,words,cell,before,layout,output,txArena,zeroArena,feeFrame,feeFrontier,feeTrace⟩:=base_fee_reached data execution
  rw [withdrawal_allocation_action] at feeTrace
  obtain ⟨wrArena,wrFrame,wrFrontier,wrTrace⟩:=allocate_field source _ current pointer record heap (withdrawalBase heap) 32#64 (ofString "wr") _
    data.arena.code feeFrame feeFrontier (by decide) (by decide) (by decide) (by decide) feeTrace
  obtain ⟨fieldsFrame,fieldsFrontier,fieldsTrace⟩:=withdrawal_fields_from_execution words data (by omega) layout wrFrame wrFrontier wrTrace
  obtain ⟨rhArena,bhArena,finalFrame,finalFrontier,same⟩:=remaining_buffers_from_execution words data (by omega) layout fieldsFrame fieldsFrontier fieldsTrace
  rw [←same] at finalFrame finalFrontier
  exact ⟨heap,hashed,words,cell,before,⟨layout,txArena,zeroArena,wrArena,rhArena,bhArena⟩,output,finalFrame,finalFrontier,same⟩

end InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry

#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.withdrawal_allocation_action
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.withdrawal_field_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.withdrawal_fields_valid
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.HeaderFrame.parent_read
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.withdrawal_fields_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.remaining_buffer_actions
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.remaining_buffers_from_execution
#print axioms InitECandidate.Solver.Input.CurrentVerify.PayloadHeaderEntry.complete_header_from_execution
