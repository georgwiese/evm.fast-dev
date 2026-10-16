import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.FFI

namespace InitECandidate.Solver.WordToStackBound.FFI
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.FFI

theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (index : Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.ffi index ptr1 len1 ptr2 len2 names) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, rfl, rfl, hc1, hc2⟩ :=
    ffiConventions k index ptr1 len1 ptr2 len2 names conventions
  simp only [compNative, Prod.mk.injEq] at compilation
  obtain ⟨rfl, -⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  refine ⟨0, ?_⟩
  rw [htarget]
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := related'
  have hvar : ∀ m v, WordSemStateFiniteExact.getVar (2 * m) source = some v → m < k →
      StackSemStateOps.getVar m target = some v := by
    intro m v hm hlt
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 (2 * m) v
      ⟨related, hm, by omega, by omega⟩
    rwa [show 2 * m / 2 = m by omega] at this
  rw [WordSemStateFiniteExact.evaluate] at execution
  rw [StackSemEvaluate.evaluate_ffi]
  simp only [show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl,
    show (6 : Nat) / 2 = 3 by rfl, show (8 : Nat) / 2 = 4 by rfl]
  rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w | ⟨_, _⟩) <;>
    rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h8 : WordSemStateFiniteExact.getVar 8 source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h6 : WordSemStateFiniteExact.getVar 6 source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h4, h2, h8, h6, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rw [hvar 2 _ h4 (by omega), hvar 1 _ h2 (by omega), hvar 4 _ h8 (by omega),
    hvar 3 _ h6 (by omega)]
  simp only [r8, r9, r15, r4]
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases hr1 : readBytearrayWordHOL w2 w.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes <;>
    rcases hr2 : readBytearrayWordHOL w4 w3.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes2 <;>
    simp only [hr1, hr2, Prod.mk.injEq] at execution ⊢ <;>
    try exact absurd execution.1.symm notError
  rcases hcall : callFFIHOL source.ffi (.extCall index) bytes bytes2 with ⟨newFfi, newBytes⟩ | outcome <;>
    simp only [hcall, Prod.mk.injEq] at execution ⊢ <;> obtain ⟨rfl, rfl⟩ := execution
  · refine ⟨_, _, Nat.zero_le _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
    have henv : env = sptUnion (sptInter source.locals names.2) (sptInter source.locals names.1) := by
      unfold wordSemCutEnv at hce
      rcases hcs : wordSemCutEnvs names source.locals with _ | ⟨e1, e2⟩
      · rw [hcs] at hce; cases hce
      rw [hcs] at hce
      obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcs
      simp only [Option.some.injEq] at hce he1 he2
      rw [← hce, ← he1, ← he2]
    unfold stateRel
    refine ⟨r1, r2, r3, rfl, r5, r6, r7, rfl, rfl, r10, r11, r12, r13, r14, rfl, rfl, r17, rfl,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      ?_, r37, r38, ?_⟩
    · show sptWf env = true
      rw [henv]
      exact sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩
    · intro m v hm
      change sptLookup m env = some v at hm
      rw [henv, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at hm
      have hlook : sptLookup m source.locals = some v ∧
          (sptDomain names.1 m ∨ sptDomain names.2 m) := by
        unfold sptDomain
        revert hm
        cases sptLookup m source.locals <;> cases sptLookup m names.2 <;>
          cases sptLookup m names.1 <;> simp
      obtain ⟨hl, hd⟩ := hlook
      have hev : m % 2 = 0 ∧ 2 * k ≤ m := hd.elim (hc1 m) (hc2 m)
      obtain ⟨he, hif⟩ := rloc m v hl
      refine ⟨he, ?_⟩
      rw [if_neg (by omega)] at hif ⊢
      exact hif
  · refine ⟨_, _, Nat.zero_le _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
    exact ⟨r4.symm, r1⟩

end InitECandidate.Solver.WordToStackBound.FFI
#print axioms InitECandidate.Solver.WordToStackBound.FFI.compCorrectFFI
