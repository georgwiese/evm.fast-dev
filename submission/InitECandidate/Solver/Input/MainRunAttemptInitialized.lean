import InitECandidate.Solver.Input.MainRunAttemptStateInitCost
import InitECandidate.Solver.Mpt.StateInitBoundaryNormal

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Actual unchanged main/run_attempt reaches its real initialized state:
closed decoded trie, workspace, eight disjoint tables and empty reserved
journal, preserved older input/header words and original hash environment.
The prefix's source allowance covers all earlier stopping outcomes. -/
theorem initialized_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (Flapjack.Basis.Pure.MlString.ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤initializationPrice input ∨
      ∃ entry current inner : PanSemStateFiniteExact 64 Guest.HostMemory,∃ workspace nodes stateRoot codes : BitVec 64,
        Mpt.StateInit.Output input entry current workspace nodes stateRoot codes ∧
        Keccak256.Environment current 2713714976#64 2713715176#64 ∧
        current.clock≤source.clock ∧ source.clock-current.clock≤initializationPrice input ∧ post.clock=inner.clock ∧
        evaluateHOLFiniteState current RunAttempt.afterStateInit=(outcome,inner):=by
  rcases state_init_entry_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨caller,inner,stateRoot,entry,target,childResult,boundary,frame,installed,scalars,rootCell,scratch,environment,forward,spent,endpoint,childRun,resumes,heapFloor⟩:=reached
    have cost:=Mpt.StateInit.body_cost input entry stateRoot boundary installed scalars rootCell scratch environment
    rw [childRun] at cost
    change entry.clock-target.clock≤Mpt.StateInit.bodyPrice input at cost
    have back:=evaluateHOLFiniteState_clock_le entry Mpt.StateInit.body
    rw [childRun] at back
    change target.clock≤entry.clock at back
    rcases resumes with stopped|normal
    · exact Or.inl (by unfold initializationPrice; rw [endpoint,stopped]; omega)
    · obtain ⟨value,resultEq,checked,continued⟩:=normal
      rw [resultEq] at childRun
      obtain ⟨zero,workspace,nodes,codes,output⟩:=Mpt.StateInit.normal_of_boundary input entry target stateRoot boundary installed scalars rootCell scratch heapFloor value childRun
      let current:={target with locals:=caller.locals}
      have currentOutput:=output.with_locals input entry target workspace nodes stateRoot codes caller.locals
      have currentEnvironment:=currentOutput.hash_environment input entry current workspace nodes stateRoot codes 2713714976#64 2713715176#64 environment
      exact Or.inr ⟨entry,current,inner,workspace,nodes,stateRoot,codes,currentOutput,currentEnvironment,back.trans forward,
        by unfold initializationPrice; change source.clock-target.clock≤_; omega,endpoint,continued⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.initialized_of_actual
