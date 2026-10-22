import InitECandidate.Solver.Input.MainRunAttemptPayloadHeaderPrefix
import InitECandidate.Solver.Input.PayloadHeaderPhysical

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact

def PayloadHeaderPhysicalReached (input : Guest.InputBlob)
    (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (outcome : Option (PanSemResultExact 64)) : Prop :=
  ∃ initializer caller entry target inner current childInner : PanSemStateFiniteExact 64 Guest.HostMemory,
    ∃ workspace nodes stateRoot codes header : BitVec 64,∃ childResult,
      PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes ∧
      PayloadHeader.PhysicalHeader input origin entry current root header ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤payloadHeaderPrefixPrice input ∧
      post.clock=inner.clock ∧ target.clock=childInner.clock ∧
      evaluateHOLFiniteState current PayloadHeader.lengthCall=(childResult,childInner) ∧
      RunAttempt.PayloadHeaderResumes caller target inner childResult outcome

/-- Actual main now reaches the original computed-size call with its
complete physical header/owned fields, true heap frontier and preserved
decoded input. Every earlier outcome keeps the existing source price. -/
theorem payload_header_physical_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤payloadHeaderPrefixPrice input ∨ PayloadHeaderPhysicalReached input origin source post root outcome := by
  rcases payload_header_prefix_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨initializer,caller,entry,target,inner,current,childInner,workspace,nodes,stateRoot,codes,childResult,
      ready,execution,forward,spent,endpoint,childEndpoint,remaining,resumes⟩:=reached
    obtain ⟨header,physical⟩:=PayloadHeader.physical_header input origin initializer entry current root workspace nodes stateRoot codes counts prepared ready execution
    exact Or.inr ⟨initializer,caller,entry,target,inner,current,childInner,workspace,nodes,stateRoot,codes,header,childResult,
      ready,physical,forward,spent,endpoint,childEndpoint,remaining,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.payload_header_physical_of_actual
