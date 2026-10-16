import InitECandidate.Solver.FlattenBound.Leaves
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Leaves

/-! Exposed extra-clock witnesses for the remaining basic Stack flattening cases.
Adapted from the pinned FlattenCorrect proofs, retaining their full hypotheses. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack.Compiler.Backend
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect

section
variable {width : Nat} [NeZero width] {C F : Type} (limit : Nat)

private theorem appList' {α : Type} (l : List α) : appListAppend (.list l) = l :=
  (appListAppend_thm .nil .nil l).2.1

/-- Shared step of `Return` and `Raise`: a register jump to a `Loc`. -/
theorem jumpRegLoc {s : StackSemStateFiniteExact width C F}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {reg l1 l2 : Nat}
    (rel : stateRel s t1)
    (fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg reg)) [] 0))
    (hreg : t1.regs reg = .loc l1 l2) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      ck ≤ 1 ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      (∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t2.code).isSome) ∧
      ∀ w, locToPc l1 l2 t2.code = some w → w = t2.pc ∧ stateRel s t2 := by
  cases hpc : locToPc l1 l2 t1.code with
  | none =>
    refine ⟨1, { t1 with clock := t1.clock + 1 }, Nat.le_refl _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, fun k hk => codeLookupLocToPc rel k hk, ?_⟩
    · simp only [Nat.add_assoc]
    · intro w hw; simp [hpc] at hw
  | some pc =>
    refine ⟨1, updPc pc t1, Nat.le_refl _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      codeLookupLocToPc rel, fun w hw => ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, hreg, hpc]
      congr 1
      simp only [updPc, decClock]
      congr 1
      omega
    · simp only [updPc] at hw ⊢
      rw [hpc] at hw
      exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `Return` case. -/
theorem flattenCorrectRet (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedProp limit (.ret v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_ret] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨ck, t2, small, run⟩ := jumpRegLoc rel fetch (InstCorrect.regOfLookup rel hv)
    exact ⟨ck, t2, small.trans (one_le_budget _ _ _ _), run⟩
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Raise` case. -/
theorem flattenCorrectRaise (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedProp limit (.raise v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_raise] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.jumpReg v)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i l1 l2 hv
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨ck, t2, small, run⟩ := jumpRegLoc rel fetch (InstCorrect.regOfLookup rel hv)
    exact ⟨ck, t2, small.trans (one_le_budget _ _ _ _), run⟩
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Break` case. -/
theorem flattenCorrectBreak (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedProp limit (.break k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, labs⟩
  rw [StackSemEvaluate.evaluate_break] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jump (.lab n (Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs))) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have some_ : (locToPc n (Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs) t1.code).isSome := by
    by_cases hm : Flapjack.Compiler.Backend.StackToLab.findLabHOL k bs ∈ bs
    · exact labs _ (by simp [hm])
    · rw [notMemFindLabImp bs k hm]; exact labs 0 (by simp)
  obtain ⟨pc, hpc⟩ := Option.isSome_iff_exists.mp some_
  refine ⟨1, updPc pc t1, one_le_budget _ _ _ _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
    codeLookupLocToPc rel, fun w hw => ?_⟩
  · rw [evaluate]
    simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue, hpc]
    congr 1
    simp only [updPc, decClock]
    congr 1
    omega
  · simp only [updPc] at hw ⊢
    rw [hpc] at hw
    exact ⟨(Option.some.inj hw).symm, rel⟩

/-- `LocValue` case. -/
theorem flattenCorrectLocValue (s1 : StackSemStateFiniteExact width C F) (reg l1 l2 : Nat) :
    BoundedProp limit (.locValue reg l1 l2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_locValue] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.locValue reg (.lab l1 l2)) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split_ifs at ev with check
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    obtain ⟨pc, hpc⟩ := StateRel.locCheckImpLocToPc ⟨check, rel⟩
    refine ⟨1, incPc (updReg reg (.loc l1 l2) t1), one_le_budget _ _ _ _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, StateRel.setVarUpdReg rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, getPcValue,
        hpc, reduceCtorEq]
      congr 1
      simp only [incPc, decClock, updReg, labToLoc]
      congr 1
      omega
    · simp [incPc, updReg, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

theorem stateRelWithCodeBuffer {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t)
    (cb : WordSemBuffer width 8) :
    stateRel { s with codeBuffer := cb } { t with codeBuffer := cb } := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, _, h23, h24, h25, h26, h27, h28, h29⟩ := rel
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
    h19, h20, h21, rfl, h23, h24, h25, h26, h27, h28, h29⟩

/-- `CodeBufferWrite` case. -/
theorem flattenCorrectCodeBufferWrite (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    BoundedProp limit (.codeBufferWrite r1 r2 : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_codeBufferWrite] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.cbw r1 r2) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have cbEq : s1.codeBuffer = t1.codeBuffer := rel.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  split at ev
  · rename_i w1 w2 h1 h2
    split at ev
    · rename_i cb hcb
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨1, incPc { t1 with codeBuffer := cb }, one_le_budget _ _ _ _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl,
        List.prefix_refl _, ?_, stateRelWithCodeBuffer rel cb⟩
      · rw [evaluate]
        simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
          InstCorrect.regOfLookup rel h1, InstCorrect.regOfLookup rel h2, ← cbEq, hcb]
        congr 1
        simp only [incPc, decClock]
        congr 1
        omega
      · simp [incPc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]
    · simp only [Prod.mk.injEq] at ev
      exact absurd ev.1.symm nerr
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Continue` case. -/
theorem flattenCorrectContinue (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedProp limit (.continue k : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_continue] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  refine ⟨0, t1, Nat.zero_le _, fun ck1 => rfl, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, rel, ?_⟩
  simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst

end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.jumpRegLoc
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectRet
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectRaise
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectBreak
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectLocValue
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectCodeBufferWrite
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectContinue
