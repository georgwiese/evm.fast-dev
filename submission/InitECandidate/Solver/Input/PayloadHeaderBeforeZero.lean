import InitECandidate.Solver.Input.PayloadHeaderScalarStores
import InitECandidate.Solver.Input.PayloadHeaderWideZero

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def scalarFields : List (Nat×Nat):=[(96,80),(104,88),(112,96),(120,104),(128,16),(136,24)]
def afterBeforeZero : List CallPrefix.Action:=afterTransactionRoot.drop 11
def transactionPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (allocatedTransactionRoot hashed heap) heap 40 (afterOmmerHeap heap)
def receiptsPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (transactionPointerStored hashed heap) heap 48 (inputPointer+62#64+84#64)
def bloomPointerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (receiptsPointerStored hashed heap) heap 56 (inputPointer+62#64+116#64)
def scalarPrefixStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  payloadFieldsStored input source heap (wideZeroStored (bloomPointerStored hashed heap) heap) scalarFields
def beforeZero (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (scalarPrefixStored input source hashed heap) heap 144 (inputPointer+62#64+372#64)

set_option maxRecDepth 100000 in
theorem before_zero_actions : afterTransactionRoot=
    .command (storeField 40 (localVar "txr"))::
    .command (storeField 48 (Scalar.plus (localVar "raw") 84))::
    .command (storeField 56 (Scalar.plus (localVar "raw") 116))::
    .command storeWideZero::
    (payloadFieldActions scalarFields++
      .command (storeField 144 (Scalar.plus (localVar "raw") 372))::afterBeforeZero) := by
  simp only [afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,
    afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterBeforeZero,payloadFieldActions,scalarFields,storeField,headerAddress,Scalar.plus,PayloadHash.fieldExpression,
    storeWideZero,wideZeroExpression,localVar,List.cons_append,List.nil_append]
  rfl

theorem scalar_fields_valid : ∀ field∈scalarFields,field.1<248 ∧ field.1%8=0 ∧ field.2<136 ∧ field.2%8=0 := by
  intro field member
  simp only [scalarFields,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl|rfl|rfl <;> decide

theorem before_zero_from_execution (input : Guest.InputBlob) (origin source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap root : BitVec 64) (counts : Nat→BitVec 64) (prepared : RequestRootHashData.Prepared input origin root counts)
    (rootBefore : root.toNat≤heap.toNat) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap hashed)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (execution : CallPrefix.Execution (allocatedTransactionRoot hashed heap) afterTransactionRoot current) :
    HeaderFrame input source heap (beforeZero input source hashed heap) ∧
      CallPrefix.Execution (beforeZero input source hashed heap) afterBeforeZero current := by
  rw [before_zero_actions] at execution
  have frame:=HeaderFrame.transaction_root input source hashed heap layout output
  have txrCell : (allocatedTransactionRoot hashed heap).locals.lookup (ofString "txr")=some (.val (.word (afterOmmerHeap heap))):=
    bind_lookup_same _ _ _
  have first:=store_field_execute (allocatedTransactionRoot hashed heap) heap 40 (afterOmmerHeap heap) (localVar "txr")
    (frame.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame.header
    (Request.local_word _ "txr" _ txrCell)
  have trace1:=execution.command_known _ _ first
  have frame1:=frame.stored input source _ heap 40 (afterOmmerHeap heap) layout.headerArena (by decide)
  have second:=store_field_execute (transactionPointerStored hashed heap) heap 48 (inputPointer+62#64+84#64)
    (Scalar.plus (localVar "raw") 84) (frame1.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame1.header
    (Scalar.plus_read _ _ _ 84 (Request.local_word _ "raw" _ frame1.raw))
  have trace2:=trace1.command_known _ _ second
  have frame2:=frame1.stored input source _ heap 48 (inputPointer+62#64+84#64) layout.headerArena (by decide)
  have third:=store_field_execute (receiptsPointerStored hashed heap) heap 56 (inputPointer+62#64+116#64)
    (Scalar.plus (localVar "raw") 116) (frame2.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame2.header
    (Scalar.plus_read _ _ _ 116 (Request.local_word _ "raw" _ frame2.raw))
  have trace3:=trace2.command_known _ _ third
  have frame3:=frame2.stored input source _ heap 56 (inputPointer+62#64+116#64) layout.headerArena (by decide)
  have wide:=wide_zero_execute (bloomPointerStored hashed heap) heap (frame3.domain.trans domain) layout.headerArena layout.headerAligned frame3.header
  have trace4:=trace3.command_known _ _ wide
  have frame4:=frame3.wide_zero input source _ heap layout.headerArena
  obtain ⟨frame5,trace5⟩:=payload_fields_from_execution input origin source heap root counts prepared rootBefore domain
    layout.headerArena layout.headerAligned scalarFields _ scalar_fields_valid _ current frame4 trace4
  have last:=store_field_execute (scalarPrefixStored input source hashed heap) heap 144 (inputPointer+62#64+372#64)
    (Scalar.plus (localVar "raw") 372) (frame5.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) frame5.header
    (Scalar.plus_read _ _ _ 372 (Request.local_word _ "raw" _ frame5.raw))
  exact ⟨frame5.stored input source _ heap 144 _ layout.headerArena (by decide),trace5.command_known _ _ last⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.before_zero_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.scalar_fields_valid
#print axioms InitECandidate.Solver.Input.PayloadHeader.before_zero_from_execution
