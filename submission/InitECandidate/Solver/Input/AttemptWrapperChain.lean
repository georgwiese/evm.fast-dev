import InitECandidate.Solver.Input.AttemptWrapperTrace

namespace InitECandidate.Solver.Input.AttemptWrapper
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A current run_attempt entry derived from the real enclosing wrappers.
All source metadata/memory/FFI fields are retained through their actual
pre-call local changes; final clocks follow the actual child execution. -/
def Reaches (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64) (depth : Nat) : Prop :=
  ∃ entry target result,entry.locals.lookup (ofString "si")=some (.val (.word si)) ∧ LocalEffects.erase entry=LocalEffects.erase source ∧
    entry.clock=source.clock-depth ∧ evaluateHOLFiniteState entry RunAttempt.body=(result,target) ∧ target.clock=post.clock

def ToRun (kind : Kind) : Prop := ∀ (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (si : BitVec 64),
  OriginalCode.Installed source.code → source.locals.lookup (ofString "si")=some (.val (.word si)) →
  ∀ outcome,evaluateHOLFiniteState source kind.body=(outcome,post) → source.clock-post.clock≤kind.ordinal ∨ Reaches source post si kind.ordinal

theorem block_to_run : ToRun .block := by
  intro source post si installed binding outcome run
  have code : source.code.lookup Kind.block.child=some (formals,RunAttempt.body,.one) := by
    simpa only [Kind.child,formals,RunAttempt.formals] using RunAttempt.original_code source.code installed
  exact trace .block source post si RunAttempt.body binding code outcome run

/-- One genuine outer wrapper composes its actual child entry with the
already checked preceding layers, without assuming any child succeeds. -/
theorem lift_to_run (kind previous : Kind) (name : kind.child=previous.name) (next : kind.ordinal=previous.ordinal+1)
    (inner : ToRun previous) : ToRun kind := by
  intro source post si installed binding outcome run
  have code : source.code.lookup kind.child=some (formals,previous.body,.one) := by rw [name]; exact original_code previous source.code installed
  rcases trace kind source post si previous.body binding code outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨entry,childPost,childResult,entrySi,frame,clock,childRun,finalClock⟩ := reached
    have entryCode:=congrArg PanSemStateFiniteExact.code frame
    change entry.code=source.code at entryCode
    have entryInstalled : OriginalCode.Installed entry.code := by rw [entryCode]; exact installed
    rcases inner entry childPost si entryInstalled entrySi childResult childRun with stopped|continued
    · have forward:=evaluateHOLFiniteState_clock_le entry previous.body
      rw [childRun] at forward
      exact Or.inl (by omega)
    · obtain ⟨last,target,result,lastSi,lastFrame,lastClock,lastRun,endpoint⟩ := continued
      refine Or.inr ⟨last,target,result,lastSi,lastFrame.trans frame,?_,lastRun,endpoint.trans finalClock⟩
      rw [clock] at lastClock
      rw [next]
      omega

/-- Complete unchanged attempt_l1..attempt_l7 chain on every outcome:
seven source caller ticks at most, or the actual run_attempt body entry. -/
theorem to_run (kind : Kind) : ToRun kind := by
  have first:=block_to_run
  have second:=lift_to_run .header .block rfl rfl first
  have third:=lift_to_run .rlp .header rfl rfl second
  have fourth:=lift_to_run .trie .rlp rfl rfl third
  have fifth:=lift_to_run .state .trie rfl rfl fourth
  have sixth:=lift_to_run .transaction .state rfl rfl fifth
  have seventh:=lift_to_run .evm .transaction rfl rfl sixth
  cases kind with
  | block=>exact first
  | header=>exact second
  | rlp=>exact third
  | trie=>exact fourth
  | state=>exact fifth
  | transaction=>exact sixth
  | evm=>exact seventh

end InitECandidate.Solver.Input.AttemptWrapper

#print axioms InitECandidate.Solver.Input.AttemptWrapper.block_to_run
#print axioms InitECandidate.Solver.Input.AttemptWrapper.lift_to_run
#print axioms InitECandidate.Solver.Input.AttemptWrapper.to_run
