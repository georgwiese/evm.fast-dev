import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Clock

namespace InitECandidate.Solver.WordToStackBound.Clock
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Clock

theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit .tick source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have related := premises.2.2.1
  have clocks : source.clock = target.clock := by
    unfold stateRel at related
    exact related.1
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  subst compiled
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  by_cases zero : source.clock = 0
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, StackSemStateOps.emptyEnv target, some .timeOut, Nat.zero_le _, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (some .timeOut, StackSemStateOps.emptyEnv target)
      rw [StackSemEvaluate.evaluate_tick, if_pos (clocks.symm.trans zero)]
    · simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
        not_true_eq_false, ↓reduceIte]
      exact ⟨related.2.2.2.1.symm, clocks⟩
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, StackSemStateOps.decClock target, none, Nat.zero_le _, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (none, StackSemStateOps.decClock target)
      have targetNonzero : target.clock ≠ 0 := fun h => zero (clocks.trans h)
      rw [StackSemEvaluate.evaluate_tick, if_neg targetNonzero]
    · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
      exact stateRelDecClock ac k f frame source target lens 0 related

theorem compCorrectMustTerminate {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (body : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.mustTerminate body) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have related := premises.2.2.1
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, termDepth, _⟩
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [termDepth, ↓reduceDIte] at execution
  have resultEq := (Prod.mk.inj execution).1
  exact False.elim (premises.2.1 resultEq.symm)

end InitECandidate.Solver.WordToStackBound.Clock
#print axioms InitECandidate.Solver.WordToStackBound.Clock.compCorrectTick
#print axioms InitECandidate.Solver.WordToStackBound.Clock.compCorrectMustTerminate
