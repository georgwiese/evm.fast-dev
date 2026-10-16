import InitECandidate.Solver.FlattenBound.Common
import Flapjack.Compiler.Backend.StackProps.ForbiddenOperations
import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps

/-! Callee syntax bounds and installation absence are preserved when both the
current code and every possible compiler-oracle extension satisfy them. The
existing evaluator's code/oracle theorem supplies the exact extension history. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

def ProgramOk {width : Nat} [NeZero width] (limit : Nat) (p : HolProg width) : Prop :=
  nodes p ≤ limit ∧ StackProps.noInstall p = true

def CodeOk {width : Nat} [NeZero width] (limit : Nat) (code : Spt (HolProg width)) : Prop :=
  ∀ key p, sptLookup key code = some p → ProgramOk limit p

def StateOk {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (s : StackSemStateFiniteExact width C F) : Prop :=
  CodeOk limit s.code ∧
    ∀ index, CodeOk limit (sptFromAList (s.compileOracle index).2.1)

theorem codeOk_union {width : Nat} [NeZero width] (limit : Nat)
    (left right : Spt (HolProg width)) (hl : CodeOk limit left) (hr : CodeOk limit right) :
    CodeOk limit (sptUnion left right) := by
  intro key p found
  rw [sptLookup_sptUnion] at found
  cases h : sptLookup key left with
  | none => simp only [h] at found; exact hr key p found
  | some body =>
    simp only [h, Option.some.injEq] at found
    subst p
    exact hl key body h

theorem codeOk_fold {width : Nat} [NeZero width] (limit : Nat)
    (trees : List (Spt (HolProg width))) (code : Spt (HolProg width))
    (initial : CodeOk limit code) (allTrees : ∀ tree ∈ trees, CodeOk limit tree) :
    CodeOk limit (trees.foldl sptUnion code) := by
  induction trees generalizing code with
  | nil => exact initial
  | cons tree trees ih =>
    exact ih (sptUnion code tree) (codeOk_union limit code tree initial (allTrees tree (by simp)))
      (fun next member => allTrees next (by simp [member]))

theorem stateOk_evaluate {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (p : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (initial : StateOk limit source)
    (execution : StackSemEvaluate.evaluate (p, source) = (result, post)) :
    StateOk limit post := by
  obtain ⟨count, oracle, code, _⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p source result post execution
  constructor
  · rw [code]
    apply codeOk_fold limit _ source.code initial.1
    intro tree member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact initial.2 index
  · intro index
    rw [oracle]
    exact initial.2 (index + count)

theorem stateOk_transport {width : Nat} [NeZero width] {C F : Type} (limit : Nat)
    (source post : StackSemStateFiniteExact width C F)
    (sameCode : post.code = source.code) (sameOracle : post.compileOracle = source.compileOracle)
    (initial : StateOk limit source) : StateOk limit post := by
  simpa only [StateOk, sameCode, sameOracle] using initial

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.codeOk_union
#print axioms InitECandidate.Solver.FlattenBound.stateOk_evaluate
