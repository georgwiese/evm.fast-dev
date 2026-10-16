import Flapjack.Compiler.Backend.StackProps.EvaluateCodeBitmaps
import Flapjack.Compiler.Backend.Semantics.StackSem.Control

/-! Static-program class for bounded Stack removal. Dynamic installation and
bitmap-driven StoreConsts copying are excluded in reachable bodies. Calls
must be direct and avoid label 6; the installed body at 6 is unrestricted. -/
namespace InitECandidate.Solver.StackRemoveDirect
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang

def directDest : Nat ⊕ Nat → Bool
  | .inl key => key != 6
  | .inr _ => false

def supported {width : Nat} [NeZero width] : HolProg width → Bool
  | .install .. | .storeConsts .. => false
  | .seq first second | .ite _ _ _ first second => supported first && supported second
  | .loop body => supported body
  | .jumpLower _ _ key | .rawCall key => key != 6
  | .call ret dest handler =>
      directDest dest && ((match ret with | none => true | some (body, _, _, _) => supported body) &&
      (match handler with | none => true | some (body, _, _) => supported body))
  | _ => true

def CodeSafe {width : Nat} [NeZero width] (code : Spt (HolProg width)) : Prop :=
  ∀ key p, key ≠ 6 → sptLookup key code = some p → supported p = true

def StateSafe {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop :=
  CodeSafe s.code ∧ ∀ index, CodeSafe (sptFromAList (s.compileOracle index).2.1)

theorem codeSafe_union {width : Nat} [NeZero width]
    (left right : Spt (HolProg width)) (hl : CodeSafe left) (hr : CodeSafe right) :
    CodeSafe (sptUnion left right) := by
  intro key p allowed found
  rw [sptLookup_sptUnion] at found
  cases h : sptLookup key left with
  | none => simp only [h] at found; exact hr key p allowed found
  | some body =>
    simp only [h, Option.some.injEq] at found
    subst p
    exact hl key body allowed h

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

theorem supported_findCode {width : Nat} [NeZero width]
    (dest : Nat ⊕ Nat) (regs : HolFiniteMapExact Nat (WordLocW width))
    (code : Spt (HolProg width)) (p : HolProg width) (safe : CodeSafe code)
    (allowed : directDest dest = true)
    (found : StackSemControl.findCode dest regs code = some p) : supported p = true := by
  cases dest with
  | inl key => exact safe key p (by simpa [directDest] using allowed) found
  | inr reg => simp [directDest] at allowed

theorem supported_return {width : Nat} [NeZero width]
    (p : HolProg width) (link l1 l2 : Nat) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ok : supported (.call (some (p, link, l1, l2)) dest handler) = true) : supported p = true := by
  rcases handler with _ | ⟨body, a, b⟩ <;>
    cases dest <;> simp_all [supported, directDest]

theorem supported_handler {width : Nat} [NeZero width]
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Nat ⊕ Nat)
    (p : HolProg width) (l1 l2 : Nat)
    (ok : supported (.call ret dest (some (p, l1, l2))) = true) : supported p = true := by
  rcases ret with _ | ⟨body, link, a, b⟩ <;>
    cases dest <;> simp_all [supported, directDest]

theorem supported_dest {width : Nat} [NeZero width]
    (ret : Option (HolProg width × Nat × Nat × Nat)) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (ok : supported (.call ret dest handler) = true) : directDest dest = true := by
  rcases ret with _ | ⟨body, link, a, b⟩ <;>
    rcases handler with _ | ⟨handlerBody, c, d⟩ <;>
    cases dest <;> simp_all [supported, directDest]

end InitECandidate.Solver.StackRemoveDirect
#print axioms InitECandidate.Solver.StackRemoveDirect.stateSafe_evaluate
#print axioms InitECandidate.Solver.StackRemoveDirect.supported_findCode
#print axioms InitECandidate.Solver.StackRemoveDirect.supported_return
#print axioms InitECandidate.Solver.StackRemoveDirect.supported_handler
