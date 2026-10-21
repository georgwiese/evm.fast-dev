import InitECandidate.Solver.Input.MainVerifyTrace
import InitECandidate.Solver.Input.VerifyConstructorPrefix

namespace InitECandidate.Solver.Input.Main.Verification
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Main's actual verification scope reaches either a bounded original
header/table prefix or a genuine state_init continuation. In both cases the
real outer serialization continuation is retained separately for costing. -/
theorem constructor_trace (input : Guest.InputBlob)
    (before copiedSource origin hashed post : PanSemStateFiniteExact 64 Guest.HostMemory) (root : BitVec 64) (counts : Nat→BitVec 64)
    (copied : InputCopied input before copiedSource)
    (actual : DecoderCall.DecoderReady input (DecoderSetup.entered copiedSource input) origin)
    (bounded : input.length%2^64≤Guest.maxInputBytes)
    (prepared : RequestRootHashData.Prepared input origin root counts) (returned : RequestHash.Returned input origin hashed root)
    (outcome : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState hashed RequestHash.continuation=(outcome,post)) :
    hashed.clock-post.clock≤1 ∨ ∃ entry target childResult,
      1≤hashed.clock ∧ LocalEffects.erase entry=LocalEffects.erase hashed ∧ entry.clock=hashed.clock-1 ∧
      evaluateHOLFiniteState entry Verify.body=(childResult,target) ∧
      (entry.clock-target.clock≤8+RunAttemptConstructors.price input ∨ ConstructorReached input entry target root) ∧
      Resumes hashed target post childResult outcome := by
  rcases trace input (DecoderSetup.entered copiedSource input) origin hashed post root actual returned outcome run with stopped|reached
  · exact Or.inl stopped
  · obtain ⟨entry,target,childResult,funded,frame,clock,si,childRun,remaining⟩ := reached
    have front:=constructor_prefix input before copiedSource origin hashed entry target root counts copied actual bounded prepared returned frame si childResult childRun
    exact Or.inr ⟨entry,target,childResult,funded,frame,clock,childRun,front,remaining⟩

end InitECandidate.Solver.Input.Main.Verification

#print axioms InitECandidate.Solver.Input.Main.Verification.constructor_trace
