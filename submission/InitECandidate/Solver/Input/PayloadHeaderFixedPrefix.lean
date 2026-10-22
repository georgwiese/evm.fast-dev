import InitECandidate.Solver.Input.PayloadHeaderStoreField
import InitECandidate.Solver.Input.PayloadHeaderHashLocals

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def afterFixedHeader : List CallPrefix.Action:=afterOmmerHash.drop 3
def ommerStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField hashed heap 16 (ommerBase heap)
def beneficiaryStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (ommerStored hashed heap) heap 24 (inputPointer+62#64+32#64)
def stateRootStored (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64):=
  storedField (beneficiaryStored hashed heap) heap 32 (inputPointer+62#64+52#64)

set_option maxRecDepth 100000 in
theorem fixed_header_actions : afterOmmerHash=
    .command (storeField 16 (localVar "oh"))::
    .command (storeField 24 (Scalar.plus (localVar "raw") 32))::
    .command (storeField 32 (Scalar.plus (localVar "raw") 52))::afterFixedHeader := by
  simp only [afterOmmerHash,afterOmmerMarker,afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,
    Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,afterFixedHeader,storeField,headerAddress,Scalar.plus,localVar]
  rfl

theorem fixed_header_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (output : OmmerHashOutput input source heap hashed)
    (domain : hashed.memaddrs=InitE.ordinaryDomain)
    (execution : CallPrefix.Execution hashed afterOmmerHash current) :
    CallPrefix.Execution (stateRootStored hashed heap) afterFixedHeader current := by
  rw [fixed_header_actions] at execution
  have hCell:=output.header_local input source hashed heap
  have ohRead:=Request.local_word hashed "oh" (ommerBase heap) (output.ommer_local input source hashed heap)
  have first:=store_field_execute hashed heap 16 (ommerBase heap) (localVar "oh") domain layout.headerArena layout.headerAligned
    (by decide) (by decide) hCell ohRead
  have firstTrace:=execution.command_known _ _ first
  have rawCell:=output.raw_local input source hashed heap
  have rawRead:=Request.local_word (ommerStored hashed heap) "raw" (inputPointer+62#64) rawCell
  have second:=store_field_execute (ommerStored hashed heap) heap 24 (inputPointer+62#64+32#64)
    (Scalar.plus (localVar "raw") 32) domain layout.headerArena layout.headerAligned (by decide) (by decide) hCell
    (Scalar.plus_read _ _ _ 32 rawRead)
  have secondTrace:=firstTrace.command_known _ _ second
  have rawRead2:=Request.local_word (beneficiaryStored hashed heap) "raw" (inputPointer+62#64) rawCell
  have third:=store_field_execute (beneficiaryStored hashed heap) heap 32 (inputPointer+62#64+52#64)
    (Scalar.plus (localVar "raw") 52) domain layout.headerArena layout.headerAligned (by decide) (by decide) hCell
    (Scalar.plus_read _ _ _ 52 rawRead2)
  exact secondTrace.command_known _ afterFixedHeader third

theorem fixed_header_older (hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap query : BitVec 64)
    (layout : OmmerLayout heap) (before : query.toNat<heap.toNat) :
    (stateRootStored hashed heap).memory query=hashed.memory query := by
  rw [stateRootStored,stored_field_older _ heap query 32 _ layout.headerArena (by decide) before,
    beneficiaryStored,stored_field_older _ heap query 24 _ layout.headerArena (by decide) before,
    ommerStored,stored_field_older _ heap query 16 _ layout.headerArena (by decide) before]

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.fixed_header_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.fixed_header_from_execution
#print axioms InitECandidate.Solver.Input.PayloadHeader.fixed_header_older
