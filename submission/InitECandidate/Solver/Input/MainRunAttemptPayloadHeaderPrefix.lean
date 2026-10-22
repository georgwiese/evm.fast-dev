import InitECandidate.Solver.Input.MainRunAttemptPayloadHeaderEntry
import InitECandidate.Solver.Input.PayloadHeaderPrefixTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact

def payloadHeaderPrefixPrice (input : Guest.InputBlob):=payloadHeaderEntryPrice input+1011

/-- Concrete nested original control flow at the block-length call. State
models are retained at the actual callee entry; the recorded action trace
is the obligation for transferring them across these fresh header writes. -/
def PayloadHeaderPrefixReached (input : Guest.InputBlob)
    (origin source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (outcome : Option (PanSemResultExact 64)) : Prop :=
  ∃ initializer caller entry target inner current childInner : PanSemStateFiniteExact 64 Guest.HostMemory,
    ∃ workspace nodes stateRoot codes : BitVec 64,∃ childResult,
      PayloadHeaderEntry input origin initializer entry root workspace nodes stateRoot codes ∧
      CallPrefix.Execution entry PayloadHeader.actions current ∧
      current.clock≤source.clock ∧ source.clock-current.clock≤payloadHeaderPrefixPrice input ∧
      post.clock=inner.clock ∧ target.clock=childInner.clock ∧
      evaluateHOLFiniteState current PayloadHeader.lengthCall=(childResult,childInner) ∧
      RunAttempt.PayloadHeaderResumes caller target inner childResult outcome

/-- Genuine unchanged main reaches the original header's computed-size
phase, or every earlier stopping path fits the accumulated source price.
No successful header prefix or prepared future header record is assumed. -/
theorem payload_header_prefix_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤payloadHeaderPrefixPrice input ∨ PayloadHeaderPrefixReached input origin source post root outcome := by
  rcases payload_header_entry_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨initializer,caller,entry,target,inner,workspace,nodes,stateRoot,codes,childResult,facts,forward,spent,endpoint,childRun,resumes⟩:=reached
    rcases PayloadHeader.prefix_trace entry target facts.state.1 childResult childRun with stopped|continued
    · obtain ⟨cost,noReturn⟩:=stopped
      rcases resumes with stopped|normal
      · exact Or.inl (by unfold payloadHeaderPrefixPrice; rw [endpoint,stopped]; omega)
      · obtain ⟨value,after,returned,checked,remaining,restored⟩:=normal
        exact (noReturn value returned).elim
    · obtain ⟨current,childInner,execution,currentForward,currentSpent,childEndpoint,remaining⟩:=continued
      exact Or.inr ⟨initializer,caller,entry,target,inner,current,childInner,workspace,nodes,stateRoot,codes,childResult,facts,execution,
        currentForward.trans forward,by unfold payloadHeaderPrefixPrice; omega,endpoint,childEndpoint,remaining,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.payload_header_prefix_of_actual
