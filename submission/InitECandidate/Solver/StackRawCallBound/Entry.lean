import InitECandidate.Solver.StackRawCallBound.Assembly
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics

namespace InitECandidate.Solver.StackRawCallBound
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

-- Actual compiled entry execution and complete FFI preservation, with at most
-- twice the source entry clock. Distinct keys and actual source code remain
-- explicit initialization obligations for the fixed guest.
theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra targetPost, extra ≤ clock - post.clock ∧ clock + extra ≤ 2 * clock ∧
      StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi := by
  have relation := CompileSemantics.initialRelation code {source with clock := clock} distinct sourceCode
  obtain ⟨extra, targetPost, space, budget, postRelation, targetRun, _⟩ :=
    (compCorrect (.call none (.inl start) none)
      {source with clock := clock}
      {source with clock := clock, code := sptFromAList (compile code)}
      (collectInfo code .ln) result post ⟨run, nonError, relation⟩).2
  refine ⟨extra, {targetPost with stackSpace := space}, by omega, by omega, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst targetPost
    rfl


end InitECandidate.Solver.StackRawCallBound
#print axioms InitECandidate.Solver.StackRawCallBound.entrySimulation
