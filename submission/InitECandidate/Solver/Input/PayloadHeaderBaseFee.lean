import InitECandidate.Solver.Input.PayloadHeaderZeroBuffer
import InitECandidate.Solver.Input.PayloadHeaderWideField
import InitECandidate.Solver.Input.CallPrefixCheckedDeclaration

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def baseFeeExpression : ExpHOL 64:=match afterZeroBuffer with | .declare _ _ expression::_=>expression | _=>.const 0#64
def afterBaseFee : List CallPrefix.Action:=afterZeroBuffer.drop 2
def feeEntry (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (words : RlpWrite.U256Value.Words):=
  setVarHOLFinite (ofString "bf") (RlpWrite.U256Value.tuple words) (zeroPointerStored input source hashed heap)
def baseFeeStored (input : Guest.InputBlob) (source hashed : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (words : RlpWrite.U256Value.Words):=wideStored (feeEntry input source hashed heap words) heap 160 words

set_option maxRecDepth 100000 in
theorem base_fee_actions : afterZeroBuffer=
    .declare (ofString "bf") RlpWrite.U256Value.tupleShape baseFeeExpression::
    .command (.store (headerAddress 160) (localVar "bf"))::afterBaseFee := by
  simp only [afterZeroBuffer,afterZeroAllocation,afterBeforeZero,afterTransactionRoot,afterFixedHeader,afterOmmerHash,afterOmmerMarker,
    afterOmmerBuffers,afterFirstStores,afterClear,afterHeader,afterReads,actions,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,
    shapeToHOL,List.map_cons,List.map_nil,Option.map_some,Option.map_none,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterBaseFee,baseFeeExpression,RlpWrite.U256Value.tupleShape,headerAddress,localVar]
  rfl

/-- A reached checked four-scalar declaration supplies the actual base fee.
All earlier declaration failures are already covered by the prefix bound. -/
theorem base_fee_from_execution (input : Guest.InputBlob) (source hashed current : PanSemStateFiniteExact 64 Guest.HostMemory)
    (heap : BitVec 64) (layout : OmmerLayout heap) (domain : source.memaddrs=InitE.ordinaryDomain)
    (frame : HeaderFrame input source heap (zeroPointerStored input source hashed heap))
    (execution : CallPrefix.Execution (zeroPointerStored input source hashed heap) afterZeroBuffer current) :
    ∃ words : RlpWrite.U256Value.Words,
      eval (zeroPointerStored input source hashed heap) baseFeeExpression=some (RlpWrite.U256Value.tuple words) ∧
      HeaderFrame input source heap (baseFeeStored input source hashed heap words) ∧
      CallPrefix.Execution (baseFeeStored input source hashed heap words) afterBaseFee current := by
  rw [base_fee_actions] at execution
  obtain ⟨words,read,next⟩:=execution.declare_words
  have feeFrame:=frame.declared input source _ heap (ofString "bf") (RlpWrite.U256Value.tuple words)
    (by decide) (by decide) (by decide) (by decide)
  have value : eval (feeEntry input source hashed heap words) (localVar "bf")=some (RlpWrite.U256Value.tuple words):=by
    simp [eval,evalHOLExact,toExact,localVar,feeEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE]
  have run:=store_wide_execute (feeEntry input source hashed heap words) heap 160 words (localVar "bf")
    (feeFrame.domain.trans domain) layout.headerArena layout.headerAligned (by decide) (by decide) feeFrame.header value
  exact ⟨words,read,feeFrame.wide_stored input source _ heap 160 words layout.headerArena (by decide),next.command_known _ _ run⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.base_fee_actions
#print axioms InitECandidate.Solver.Input.PayloadHeader.base_fee_from_execution
