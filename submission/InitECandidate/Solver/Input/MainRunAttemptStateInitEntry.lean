import InitECandidate.Solver.Input.MainStateInitEntryData
import InitECandidate.Solver.Input.MainRunAttemptStateInitBoundary
import InitECandidate.Solver.Input.RunAttemptStateInitCallTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The actual unchanged run_attempt prefix either stops within its real
header/table/caller allowance or enters the genuine state_init322 body with
all physical/runtime data and its real root word. Both failure and normal
outer continuations remain connected to the same observed execution. -/
theorem state_init_entry_of_actual (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source RunAttempt.body=(outcome,post)) :
    source.clock-post.clock≤price input+1 ∨ ∃ caller inner stateRoot entry target childResult,
      StateInitBoundary input entry ∧ ConstructorRuntimeFrame source entry ∧
      OriginalCode.Installed entry.code ∧ OriginalScalarGlobals.Scalars entry.globals ∧
      entry.locals.lookup (ofString "state_root")=some (.val (.word stateRoot)) ∧
      Rlp.Validation.Arena entry 2713714688#64 2701135872#64 ∧ Keccak256.Environment entry 2713714976#64 2713715176#64 ∧
      entry.clock≤source.clock ∧ source.clock-entry.clock≤price input+1 ∧ post.clock=inner.clock ∧
      evaluateHOLFiniteState entry Mpt.StateInit.body=(childResult,target) ∧ RunAttempt.StateInitResumes caller target inner childResult outcome := by
  rcases state_init_boundary_of_actual input before copiedSource origin hashed source post root counts copied actual bounded prepared returned entryFrame siCell outcome run with stopped|reached
  · exact Or.inl (stopped.trans (Nat.le_add_right _ _))
  · obtain ⟨caller,inner,boundary,frame,installed,scalars,arena,environment,forward,spent,endpoint,remaining⟩ := reached
    have callerBoundary:=boundary
    obtain ⟨codeArray,nodes,codes,heap,nodeDatabase,codeDatabase,nodeCell,codeCell,heapCell,heapArena,aligned,nodeBefore,codeBefore⟩ := boundary
    rcases RunAttempt.state_init_call_trace caller inner nodes codes installed nodeCell codeCell outcome remaining with stopped|observed
    · have back:=evaluateHOLFiniteState_clock_le caller RunAttempt.afterCodes
      rw [remaining] at back
      rw [endpoint]
      exact Or.inl (by omega)
    · obtain ⟨stateRoot,entry,target,childResult,rootRead,pure,clock,nodesEntry,rootEntry,codesEntry,childRun,resumes⟩ := observed
      have entryData:=StateInitBoundary.at_entry input caller entry callerBoundary pure (nodesEntry.trans nodeCell.symm) (codesEntry.trans codeCell.symm)
      have entryRuntime:=runtime_of_entry caller entry pure
      have wholeFrame:=frame.trans source caller entry entryRuntime
      have entryInstalled : OriginalCode.Installed entry.code := by rw [entryRuntime.code]; exact installed
      have globals:=congrArg PanSemStateFiniteExact.globals pure
      change entry.globals=caller.globals at globals
      have entryScalars : OriginalScalarGlobals.Scalars entry.globals := by rw [globals]; exact scalars
      have entryArena:=entryRuntime.scratch caller entry 2713714688#64 2701135872#64 arena
      have entryEnvironment:=entryRuntime.hash_environment caller entry 2713714976#64 2713715176#64 environment
      exact Or.inr ⟨caller,inner,stateRoot,entry,target,childResult,entryData,wholeFrame,entryInstalled,entryScalars,rootEntry,entryArena,entryEnvironment,
        by omega,by omega,endpoint,childRun,resumes⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.state_init_entry_of_actual
