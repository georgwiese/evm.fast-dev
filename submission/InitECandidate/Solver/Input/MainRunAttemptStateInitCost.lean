import InitECandidate.Solver.Input.MainRunAttemptStateInitEntry
import InitECandidate.Solver.Mpt.StateInitBodyCost

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

def initializationPrice (input : Guest.InputBlob) : Nat:=price input+1+Mpt.StateInit.bodyPrice input

/-- Real original run_attempt prefix through the complete state_init call.
Every stopped child is included. A genuine return reaches the actual next
program with the summed allowance already paid; no successful initializer
or supplied future callee execution is an entry premise. -/
theorem after_state_init_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤initializationPrice input ∨ ∃ current inner : PanSemStateFiniteExact 64 Guest.HostMemory,
      OriginalCode.Installed current.code ∧ current.clock≤source.clock ∧
      source.clock-current.clock≤initializationPrice input ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState current RunAttempt.afterStateInit=(outcome,inner):=by
  rcases state_init_entry_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨caller,inner,stateRoot,entry,target,childResult,boundary,frame,installed,scalars,rootCell,scratch,environment,forward,spent,endpoint,childRun,resumes⟩:=reached
    have cost:=Mpt.StateInit.body_cost input entry stateRoot boundary installed scalars rootCell scratch environment
    rw [childRun] at cost
    change entry.clock-target.clock≤Mpt.StateInit.bodyPrice input at cost
    have back:=evaluateHOLFiniteState_clock_le entry Mpt.StateInit.body
    rw [childRun] at back
    change target.clock≤entry.clock at back
    have fields:=evaluation_fields entry target Mpt.StateInit.body childResult childRun
    rcases resumes with stopped|normal
    · exact Or.inl (by unfold initializationPrice; rw [endpoint,stopped]; omega)
    · obtain ⟨value,resultEq,checked,continued⟩:=normal
      let current:={target with locals:=caller.locals}
      have currentInstalled : OriginalCode.Installed current.code:=by rewrite [show current.code=entry.code from fields.2.2.2]; exact installed
      exact Or.inr ⟨current,inner,currentInstalled,back.trans forward,by unfold initializationPrice; change source.clock-target.clock≤_; omega,endpoint,continued⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.after_state_init_of_actual
