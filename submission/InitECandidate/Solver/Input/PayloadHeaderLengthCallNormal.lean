import InitECandidate.Solver.Input.PayloadHeaderLengthNormal
import InitECandidate.Solver.Input.RlpLength.BlockGuardNormal
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Main

def afterSizeGuard : ProgHOL 64:=match afterLength with | .seq _ rest=>rest | _=>.skip

set_option maxRecDepth 100000 in
theorem length_guard_shape : afterLength=.seq RlpLength.Block.sizeGuard afterSizeGuard := by
  simp only [afterLength,lengthCall,parts,body,Guest.guestFn_payload_header,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil,
    Option.map_none,Option.map_some,CallPrefix.cut,
    show ofString "alloc"≠ofString "block_rlp_length" from by decide,if_false,if_true,
    afterSizeGuard,RlpLength.Block.sizeGuard,RlpLength.Block.sizeTest,localVar] <;>rfl

/-- The actual scoped block-length return and original size guard derive
the accepted encoded-size/withdrawal caps, real continuation and caller
cost. Neither space, clock funding nor future helper success is supplied. -/
theorem length_call_normal (input : Guest.InputBlob) (before copiedSource origin source current post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root header : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (physical : PhysicalHeader input origin source current root header)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState current lengthCall=(some (.returned value),post)) :
    ∃ callee target encoded inner,
      encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧
      evaluateHOLFiniteState (callEntryStateHOLFinite current callee) RlpLength.Block.body=
        (some (.returned (.val (.word (BitVec.ofNat 64 encoded)))),target) ∧
      current.clock-target.clock≤RlpLength.Block.price input (lengthTxStart input) (Payload.transactionBytes input) (Payload.withdrawalCount input)+1 ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry current target "bl" (.val (.word (BitVec.ofNat 64 encoded)))) afterLength=(some (.returned value),inner) ∧
      post=restore current "bl" inner ∧
      emptyLocalsHOLFinite target=emptyLocalsHOLFinite {current with memory:=target.memory,clock:=target.clock} ∧
      HeaderEncoding.OldMemory target.memory current.memory (headerFrontier header) ∧
      evaluateHOLFiniteState (CallNormal.continuationEntry current target "bl" (.val (.word (BitVec.ofNat 64 encoded)))) afterSizeGuard=(some (.returned value),inner) := by
  obtain ⟨callee,called,hdr,pl⟩:=RlpLength.Block.environment current.code.lookup header (PayloadPrefix.cursor input)
    (OriginalRlp.block_rlp_length current.code physical.installed)
  have args : evalListHOLFinite current (h:=fun address=>Classical.propDecidable (current.memaddrs address))
      [localVar "h",localVar "pl"]=some [.val (.word header),.val (.word (PayloadPrefix.cursor input))]:=by
    have hCell:=physical.frame.header
    have plCell:=physical.frame.payload
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,hCell,plCell]
  rw [length_call_shape] at normal
  obtain ⟨funded,target,returned,inner,childRun,checked,remaining,restored⟩:=CallNormal.scoped_normal current post "bl" .one (ofString "block_rlp_length")
    [localVar "h",localVar "pl"] [.val (.word header),.val (.word (PayloadPrefix.cursor input))] RlpLength.Block.body afterLength callee .one args called value normal
  obtain ⟨encoded,minimum,maximum,number,valueEq,cost,frame,old⟩:=length_body_normal input before copiedSource origin source current target
    root header counts copied actual bounded prepared physical callee called returned childRun
  rw [valueEq] at childRun remaining
  let continued:=CallNormal.continuationEntry current target "bl" (.val (.word (BitVec.ofNat 64 encoded)))
  have bl : continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))):=bind_lookup_same _ _ _
  have guarded:=remaining
  rw [length_guard_shape] at guarded
  have size:=RlpLength.Block.guarded_normal continued inner encoded afterSizeGuard value bl number guarded
  have callerCost : current.clock-target.clock≤RlpLength.Block.price input (lengthTxStart input) (Payload.transactionBytes input) (Payload.withdrawalCount input)+1:=by
    have forward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite current callee) RlpLength.Block.body
    rw [childRun] at forward
    change target.clock≤current.clock-1 at forward
    change current.clock-1-target.clock≤_ at cost
    omega
  have passed:=RlpLength.Block.guard_pass continued encoded bl number size
  have tailRun : evaluateHOLFiniteState continued afterSizeGuard=(some (.returned value),inner):=by
    rw [WitnessRadix.StateSteps.next_sequence continued continued _ _ passed (Nat.le_refl _)] at guarded
    exact guarded
  exact ⟨callee,target,encoded,inner,size,by omega,childRun,callerCost,remaining,restored,frame,old,tailRun⟩

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.length_guard_shape
#print axioms InitECandidate.Solver.Input.PayloadHeader.length_call_normal
