import InitECandidate.Solver.Input.MainRunAttemptConstructorPrefix
import InitECandidate.Solver.Input.VerifyTrace

namespace InitECandidate.Solver.Input.Main.Verification
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The real run_attempt body reached through all eight original catch
layers, together with its genuine state_init continuation after both tables. -/
def ConstructorReached (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) : Prop :=
  ∃ entry target result, LocalEffects.erase entry=LocalEffects.erase source ∧ entry.clock=source.clock-8 ∧
    evaluateHOLFiniteState entry RunAttempt.body=(result,target) ∧ target.clock=post.clock ∧
    RunAttemptConstructors.Reached input entry target root result

/-- Compose actual decoded main data, all eight unchanged catch layers and
the complete original header/database prefix. No successful body is assumed. -/
theorem constructor_prefix (input : Guest.InputBlob)
    (before copiedSource origin hashed source post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (entryFrame : LocalEffects.erase source=LocalEffects.erase hashed)
    (siCell : source.locals.lookup (ofString "si")=some (.val (.word (RequestPrefix.cursor input))))
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source Verify.body=(outcome,post)) :
    source.clock-post.clock≤8+RunAttemptConstructors.price input ∨ ConstructorReached input source post root := by
  have code:=LocalEffects.code_of_erase hashed source entryFrame
  have installed : OriginalCode.Installed source.code := by rw [code]; exact returned.workspace.sha.installed
  rcases Verify.to_run source post (RequestPrefix.cursor input) installed siCell outcome run with stopped|reached
  · exact Or.inl (by omega)
  · obtain ⟨entry,target,result,entrySi,frame,clock,childRun,endpoint⟩ := reached
    rcases RunAttemptConstructors.prefix_of_actual input before copiedSource origin hashed entry target root counts copied actual bounded prepared returned
      (frame.trans entryFrame) entrySi result childRun with stopped|continued
    · have forward:=evaluateHOLFiniteState_clock_le entry RunAttempt.body
      rw [childRun] at forward
      exact Or.inl (by omega)
    · exact Or.inr ⟨entry,target,result,frame,clock,childRun,endpoint,continued⟩

end InitECandidate.Solver.Input.Main.Verification

#print axioms InitECandidate.Solver.Input.Main.Verification.constructor_prefix
