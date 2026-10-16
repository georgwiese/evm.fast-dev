import InitECandidate.Solver.StackRawCallBound.Standard
import InitECandidate.Solver.StackRawCallBound.Optimized
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompSeqShape

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall
open Flapjack.Compiler.Backend.StackRawCall.SeqCase

theorem compCorrectSeq {width : Nat} [NeZero width] {C F : Type}
    (first second : HolProg width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (firstIH : BoundedProgramIH C F first source)
    (secondIH : BoundedSeqSecondIH C F first second source)
    (hypothesis : StackSemEvaluate.evaluate (.seq first second, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulation 0 (source.clock - post.clock) (compTop info (.seq first second)) info target post result ∧
    BoundedSimulation 0 (source.clock - post.clock) (comp info (.seq first second)) info target post result := by
  have standard := simulateStandardSeq first second info source target post result
    firstIH secondIH hypothesis
  constructor
  · simpa only [compTop] using standard
  · change BoundedSimulation 0 (source.clock - post.clock) (compSeq first second info (.seq (comp info first) (comp info second)))
      info target post result
    by_cases fallback : compSeq first second info (.seq (comp info first) (comp info second)) =
        .seq (comp info first) (comp info second)
    · rw [fallback]
      exact standard
    · obtain ⟨released, dest, rfl, rfl⟩ := compSeqNeqImp first second
        (.seq (comp info first) (comp info second)) info fallback
      cases frame : sptLookup dest info with
      | none => simp [compSeq, destCase, frame] at fallback
      | some allocated =>
          simpa only [compSeq, destCase, frame] using
            simulateOptimizedSeq released allocated dest info source target post result
              frame secondIH hypothesis


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.compCorrectSeq
