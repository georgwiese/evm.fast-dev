import InitECandidate.Solver.FlattenWeighted.BlockBound
import InitECandidate.Solver.FlattenWeighted.NoException

namespace InitECandidate.Solver.FlattenWeighted
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open StackSemEvaluate StackSemStateOps StackSemControl

/-- Clock cost of a returning call whose actual callee cannot raise. The
callee and selected continuation bounds apply to their actual entry states. -/
theorem returningCallClock {width : Nat} [NeZero width] {C F : Type}
    (callee continuation : HolProg width) (destination link label offset : Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F) (calleeClocks returnClocks : Nat)
    (installed : sptLookup destination source.code = some callee)
    (calleeClock :
      (decClock (setVar link (.loc label offset) source)).clock ≤
      (evaluate (callee, decClock (setVar link (.loc label offset) source))).2.clock + calleeClocks)
    (calleeSafe : ∀ value,
      (evaluate (callee, decClock (setVar link (.loc label offset) source))).1 ≠ some (.exception value))
    (returnClock : ∀ next,
      evaluate (callee, decClock (setVar link (.loc label offset) source)) =
        (some (.result (.loc label offset)), next) →
      next.clock ≤ (evaluate (continuation, next)).2.clock + returnClocks) :
    source.clock ≤
      (evaluate (.call (some (continuation, link, label, offset)) (.inl destination) handler, source)).2.clock +
        (1 + calleeClocks + returnClocks) := by
  rw [evaluate_call]
  simp only [findCode, installed]
  by_cases zero : source.clock = 0
  · simp [zero]
  simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate]
  rcases run : evaluate (callee, decClock (setVar link (.loc label offset) source)) with ⟨result, next⟩
  rw [run] at calleeClock calleeSafe
  dsimp only [decClock, setVar, Prod.snd] at calleeClock
  cases result with
  | none => dsimp only; omega
  | some outcome =>
    cases outcome with
    | result value =>
      by_cases same : value = .loc label offset
      · subst value
        simp only [ne_eq, not_true_eq_false, if_false]
        have bounded := returnClock next run
        omega
      · simp only [same, ne_eq, not_false_eq_true, if_true, Prod.snd]
        omega
    | exception value => exact (calleeSafe value rfl).elim
    | _ => dsimp only; omega

/-- Timeout in a non-raising returning call leaves zero clock when both
its callee and its selected return continuation have this property. -/
theorem returningCallTimeout {width : Nat} [NeZero width] {C F : Type}
    (callee continuation : HolProg width) (destination link label offset : Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (source : StackSemStateFiniteExact width C F)
    (installed : sptLookup destination source.code = some callee)
    (calleeSafe : ∀ value,
      (evaluate (callee, decClock (setVar link (.loc label offset) source))).1 ≠ some (.exception value))
    (calleeZero : ∀ next,
      evaluate (callee, decClock (setVar link (.loc label offset) source)) = (some .timeOut, next) →
      next.clock = 0)
    (returnZero : ∀ middle next,
      evaluate (callee, decClock (setVar link (.loc label offset) source)) =
        (some (.result (.loc label offset)), middle) →
      evaluate (continuation, middle) = (some .timeOut, next) → next.clock = 0)
    (post : StackSemStateFiniteExact width C F)
    (execution : evaluate (.call (some (continuation, link, label, offset))
      (.inl destination) handler, source) = (some .timeOut, post)) : post.clock = 0 := by
  rw [evaluate_call] at execution
  simp only [findCode, installed] at execution
  by_cases zero : source.clock = 0
  · simp only [zero, if_true, Prod.mk.injEq, true_and] at execution
    subst post
    simpa [emptyEnv] using zero
  simp only [zero, if_false, StackSemEvaluateClock.fixClockEvaluate] at execution
  rcases run : evaluate (callee, decClock (setVar link (.loc label offset) source)) with ⟨result, next⟩
  rw [run] at execution calleeSafe
  cases result with
  | none => simp at execution
  | some outcome =>
    cases outcome with
    | result value =>
      by_cases same : value = .loc label offset
      · subst value
        simp only [ne_eq, not_true_eq_false, if_false] at execution
        exact returnZero next post run execution
      · simp [same] at execution
    | exception value => exact (calleeSafe value rfl).elim
    | timeOut =>
      have equal : next = post := congrArg Prod.snd execution
      subst post
      exact calleeZero next run
    | _ => simp at execution

end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.returningCallClock
#print axioms InitECandidate.Solver.FlattenWeighted.returningCallTimeout
