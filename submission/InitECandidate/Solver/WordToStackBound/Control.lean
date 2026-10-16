import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Control

namespace InitECandidate.Solver.WordToStackBound.Control
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect

theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit .skip source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, none, Nat.zero_le _, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_skip]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (label : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.break label) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, some (.break label), Nat.zero_le _, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_break]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (label : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.continue label) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, target, some (.continue label), Nat.zero_le _, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_continue]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

end InitECandidate.Solver.WordToStackBound.Control
#print axioms InitECandidate.Solver.WordToStackBound.Control.compCorrectSkip
#print axioms InitECandidate.Solver.WordToStackBound.Control.compCorrectBreak
#print axioms InitECandidate.Solver.WordToStackBound.Control.compCorrectContinue
