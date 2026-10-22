import InitECandidate.Solver.Input.PayloadHeaderAfterLength
import InitECandidate.Solver.Input.PayloadHeaderPrefixTrace

namespace InitECandidate.Solver.Input.PayloadHeader
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString Main Main.RunAttemptConstructors

def normalPrefixPrice (input : Guest.InputBlob):=1011+
  (RlpLength.Block.price input (lengthTxStart input) (Payload.transactionBytes input) (Payload.withdrawalCount input)+1)

/-- A real normal payload_header reaches its original indexed-trie call
after computing and passing the size guard. Main supplies its physical
header/input/output buffers; the actual guard supplies the withdrawal cap. -/
theorem normal_trie_entry (input : Guest.InputBlob) (before copiedSource origin initializer source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (root workspace nodes stateRoot codes : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts)
    (ready : PayloadHeaderEntry input origin initializer source root workspace nodes stateRoot codes)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    ∃ header continued inner encoded,
      PhysicalHeader input origin source continued root header ∧ encoded≤8388608 ∧ Payload.withdrawalCount input≤335544 ∧
      continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))) ∧
      continued.clock≤source.clock ∧ source.clock-continued.clock≤normalPrefixPrice input ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState continued afterSizeGuard=(some (.returned value),inner) := by
  rcases prefix_trace source post ready.state.1 (some (.returned value)) normal with stopped|reached
  · exact (stopped.2 value rfl).elim
  · obtain ⟨current,childInner,execution,forward,spent,endpoint,remaining⟩:=reached
    obtain ⟨header,physical⟩:=physical_header input origin initializer source current root workspace nodes stateRoot codes counts prepared ready execution
    obtain ⟨callee,target,encoded,inner,size,withdrawals,childRun,cost,afterLengthRun,restored,control,old,tailRun⟩:=
      length_call_normal input before copiedSource origin source current childInner root header counts copied actual bounded prepared physical value remaining
    let continued:=CallNormal.continuationEntry current target "bl" (.val (.word (BitVec.ofNat 64 encoded)))
    have finalPhysical:=physical.after_length input origin source current target root header (.val (.word (BitVec.ofNat 64 encoded))) control old
    have childForward:=evaluateHOLFiniteState_clock_le (callEntryStateHOLFinite current callee) RlpLength.Block.body
    rw [childRun] at childForward
    change target.clock≤current.clock-1 at childForward
    have clock:=congrArg PanSemStateFiniteExact.clock restored
    change childInner.clock=inner.clock at clock
    have bl : continued.locals.lookup (ofString "bl")=some (.val (.word (BitVec.ofNat 64 encoded))):=
      WitnessRadix.QueryBranch.bind_lookup_same _ _ _
    refine ⟨header,continued,inner,encoded,finalPhysical,size,withdrawals,bl,?_,?_,endpoint.trans clock,tailRun⟩
    · change target.clock≤source.clock
      omega
    · change source.clock-target.clock≤_
      unfold normalPrefixPrice
      omega

end InitECandidate.Solver.Input.PayloadHeader

#print axioms InitECandidate.Solver.Input.PayloadHeader.normal_trie_entry
