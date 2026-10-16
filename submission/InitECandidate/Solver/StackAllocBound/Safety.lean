import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Program class for zero-clock allocation lowering. Allocation, installation
and stubbed StoreConsts are explicitly excluded; all other syntax
constructors retain their original semantics and guards. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

def eligible {width : Nat} [NeZero width] : HolProg width → Bool
  | .alloc .. | .install .. | .storeConsts _ _ (some _) => false
  | .seq first second | .ite _ _ _ first second => eligible first && eligible second
  | .loop body => eligible body
  | .call ret _ handler =>
      (match ret with | none => true | some (body, _, _, _) => eligible body) &&
      (match handler with | none => true | some (body, _, _) => eligible body)
  | _ => true

def CodeSafe {width : Nat} [NeZero width] (code : Spt (HolProg width)) : Prop :=
  ∀ key p, sptLookup key code = some p → eligible p = true

def StateSafe {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop :=
  CodeSafe s.code ∧ ∀ index, CodeSafe (sptFromAList (s.compileOracle index).2.1)

theorem codeSafe_union {width : Nat} [NeZero width]
    (left right : Spt (HolProg width)) (hl : CodeSafe left) (hr : CodeSafe right) :
    CodeSafe (sptUnion left right) := by
  intro key p found
  rw [sptLookup_sptUnion] at found
  cases h : sptLookup key left with
  | none => simp only [h] at found; exact hr key p found
  | some body =>
    simp only [h, Option.some.injEq] at found
    subst p
    exact hl key body h

theorem codeSafe_fold {width : Nat} [NeZero width]
    (trees : List (Spt (HolProg width))) (code : Spt (HolProg width))
    (initial : CodeSafe code) (allTrees : ∀ tree ∈ trees, CodeSafe tree) :
    CodeSafe (trees.foldl sptUnion code) := by
  induction trees generalizing code with
  | nil => exact initial
  | cons tree trees ih =>
    exact ih (sptUnion code tree) (codeSafe_union code tree initial (allTrees tree (by simp)))
      (fun next member => allTrees next (by simp [member]))

theorem stateSafe_evaluate {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (source post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (initial : StateSafe source)
    (execution : StackSemEvaluate.evaluate (p, source) = (result, post)) : StateSafe post := by
  obtain ⟨count, oracle, code, _⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p source result post execution
  constructor
  · rw [code]
    apply codeSafe_fold _ source.code initial.1
    intro tree member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact initial.2 index
  · intro index
    rw [oracle]
    exact initial.2 (index + count)

theorem eligible_findCode {width : Nat} [NeZero width]
    (dest : Nat ⊕ Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (code : Spt (HolProg width)) (p : HolProg width) (safe : CodeSafe code)
    (found : StackSemControl.findCode dest regs code = some p) : eligible p = true := by
  cases dest with
  | inl key => exact safe key p found
  | inr reg =>
    simp only [StackSemControl.findCode] at found
    split at found
    · exact safe _ p found
    · simp at found

theorem eligible_return {width : Nat} [NeZero width]
    (p : HolProg width) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ok : eligible (.call (some (p, link, l1, l2)) dest handler) = true) : eligible p = true := by
  rcases handler with _ | ⟨body, a, b⟩
  · simpa only [eligible, Bool.and_true] using ok
  · exact (Bool.and_eq_true_iff.mp ok).1

theorem eligible_handler {width : Nat} [NeZero width]
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Nat ⊕ Nat)
    (p : HolProg width) (l1 l2 : Nat)
    (ok : eligible (.call ret dest (some (p, l1, l2))) = true) : eligible p = true := by
  rcases ret with _ | ⟨body, link, a, b⟩
  · simpa only [eligible, Bool.true_and] using ok
  · exact (Bool.and_eq_true_iff.mp ok).2

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.stateSafe_evaluate
#print axioms InitECandidate.Solver.StackAllocBound.eligible_findCode
#print axioms InitECandidate.Solver.StackAllocBound.eligible_return
#print axioms InitECandidate.Solver.StackAllocBound.eligible_handler
