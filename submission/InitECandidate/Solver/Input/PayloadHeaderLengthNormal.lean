import InitECandidate.Solver.Input.PayloadHeaderLengthGeometry
import InitECandidate.Solver.Input.PayloadHeaderLengthRegions
import InitECandidate.Solver.Input.RlpLength.BlockCurrent

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main

/-- At the actual original block-length child, main derives all data,
field ownership, temporary-space, code and local-binding premises. The
real normal return supplies its length, source cost and memory frame. -/
theorem length_body_normal (input : Guest.InputBlob) (before copiedSource origin source current target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (called : lookupCodeHOLFinite current.code.lookup (ofString "block_rlp_length")
      [.val (.word header),.val (.word (PayloadPrefix.cursor input))]=some (RlpLength.Block.body,callee,.one))
    (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState (callEntryStateHOLFinite current callee) RlpLength.Block.body=(some (.returned value),target)) :
    ∃ encoded,25*Payload.withdrawalCount input≤encoded ∧ encoded≤436208508+57*Payload.withdrawalCount input ∧
      (BitVec.ofNat 64 encoded).toNat=encoded ∧ value=.val (.word (BitVec.ofNat 64 encoded)) ∧
      (callEntryStateHOLFinite current callee).clock-target.clock≤
        RlpLength.Block.price input (lengthTxStart input) (Payload.transactionBytes input) (Payload.withdrawalCount input) ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {current with memory:=target.memory,clock:=target.clock} ∧
      HeaderEncoding.OldMemory target.memory current.memory (headerFrontier header) := by
  obtain ⟨expected,expectedCall,hdr,pl⟩:=RlpLength.Block.environment current.code.lookup header (PayloadPrefix.cursor input)
    (OriginalRlp.block_rlp_length current.code physical.installed)
  have equal:=Option.some.inj (called.symm.trans expectedCall)
  have mapEq:=congrArg (fun triple : ProgHOL 64×HolFiniteMapExact MlS (ValueHOL 64)×ShapeHOL=>triple.2.1) equal
  change callee=expected at mapEq
  subst callee
  let entry:=callEntryStateHOLFinite current expected
  have data:=rlp_data input before copiedSource origin source current root header counts copied actual bounded prepared physical
  have entryData:=RlpLength.Block.Data.of_fields current entry input inputPointer (lengthArray input) (PayloadPrefix.cursor input)
    (lengthTxStart input) (Payload.transactionBytes input) (lengthWdStart input) (Payload.withdrawalCount input) rfl rfl rfl data
  have geometry:=length_geometry input origin source current target root header physical expected value normal
  obtain ⟨inputBefore,arrayBefore,cellsBefore⟩:=length_regions input (DecoderSetup.entered copiedSource input) origin source current root header counts actual bounded prepared physical
  have codes:=OriginalRlp.block_codes current physical.installed
  exact RlpLength.Block.body_normal entry target input inputPointer (lengthArray input) (PayloadPrefix.cursor input) header (headerFrontier header)
    (lengthTxStart input) (Payload.transactionBytes input) (lengthWdStart input) (Payload.withdrawalCount input) physical.domain entryData geometry
    inputBefore arrayBefore cellsBefore hdr pl physical.frontier.cell (RlpLength.Block.Codes.of_code current entry rfl codes)
    physical.fields (by intro nonzero; exact physical.optional) value normal

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.length_body_normal
