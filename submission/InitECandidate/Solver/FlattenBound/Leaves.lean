import InitECandidate.Solver.FlattenBound.Common
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Leaves

/-! Exposed 0/1 extra-clock witnesses for four basic Stack flattening cases.
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

theorem flattenCorrectSkip (s1 : StackSemStateFiniteExact width C F) :
    BoundedProp limit (.skip : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, -, rel, -, -, -⟩
  rw [StackSemEvaluate.evaluate_skip] at ev
  cases ev
  refine ⟨0, t1, Nat.zero_le _, ?_⟩
  simp only [haltView, Option.map_none, true_and]
  exact ⟨fun ck1 => by simp, List.prefix_refl _, by simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'], rel⟩

/-- `Halt` case. -/
theorem flattenCorrectHalt (s1 : StackSemStateFiniteExact width C F) (v : Nat) :
    BoundedProp limit (.halt v : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, -⟩
  rw [StackSemEvaluate.evaluate_halt] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm .halt 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  simp only [StackProps.callArgs] at ca
  split at ev
  · rename_i w hw
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have hreg : t1.regs t1.ptrReg = w := by
      rw [← ca]; exact InstCorrect.regOfLookup rel hw
    refine ⟨1, { t1 with clock := t1.clock + 1 }, one_le_budget _ _ _ _, ?_, ?_⟩
    · rw [evaluate]
      simp only [Nat.add_one_ne_zero, if_false, asmFetch, fetch, hreg]
      cases w with
      | word value =>
        by_cases hv : value = 0#width
        · simp [haltWordView, hv]
        · simp [haltWordView, hv]
      | loc a b => simp [haltWordView]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- `Inst` case. -/
theorem flattenCorrectInst (s1 : StackSemStateFiniteExact width C F) (i : HolInst width) :
    BoundedProp limit (.inst i : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_inst] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst i)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  split at ev
  · rename_i s1' hi
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have rel2 := InstCorrect.instCorrect ⟨hi, rel⟩
    obtain ⟨cpc, ccode, cclock, -, -, -, -, -, cptr, clen, cptr2, clen2, clink⟩ :=
      asmInstConsts i t1
    have nf := InstCorrect.notFailed rel2
    refine ⟨1, incPc (asmInst i t1), one_le_budget _ _ _ _, fun ck1 => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rel2⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch,
        LabProps.asmInstWithClock, nf, Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock, cclock, cpc]
      congr 1 <;> first | omega | exact nf.symm
    all_goals simp [incPc, cptr, clen, cptr2, clen2, clink, ccode, cpc, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList',
      isLabelHOL]
  · simp only [Prod.mk.injEq] at ev
    exact absurd ev.1.symm nerr

/-- Every installed StackSem procedure has a LabSem entry position. -/
theorem codeLookupLocToPc {s : StackSemStateFiniteExact width C F}
    {t : Flapjack.Compiler.Backend.LabSem.State width C F} (rel : stateRel s t) :
    ∀ k, (sptLookup k s.code).isSome → (locToPc k 0 t.code).isSome := by
  intro k hk
  obtain ⟨prog, hp⟩ := Option.isSome_iff_exists.mp hk
  obtain ⟨-, pc, -, entry⟩ := rel.2.2.2.2.2.2.2.2.1 k prog hp
  simp [entry]

/-- `Tick` case. -/
theorem flattenCorrectTick (s1 : StackSemStateFiniteExact width C F) :
    BoundedProp limit (.tick : HolProg width) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_tick] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.asm (.asmi (.inst .skip)) [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList'] using inst)
  have nf := InstCorrect.notFailed rel
  have clk := relClock rel
  split_ifs at ev with h0
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨1, incPc t1, one_le_budget _ _ _ _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · rw [evaluate]
      simp only [show t1.clock + 1 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, StackSemStateOps.emptyEnv, relFfi rel]
    · simp [incPc]; omega
  · simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, incPc (decClock t1), Nat.zero_le _, fun ck1 => ?_, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _,
      ?_, StateRel.stateRelDecClock rel⟩
    · rw [evaluate]
      simp only [show t1.clock + 0 + ck1 ≠ 0 by omega, if_false, asmFetch, fetch, asmInst, nf,
        Bool.false_eq_true]
      congr 1
      simp only [incPc, decClock]
      congr 1 <;> first | omega | exact nf.symm
    · simp [incPc, decClock, Flapjack.Compiler.Backend.StackToLab.flattenHOL, appList', isLabelHOL]


end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectSkip
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectHalt
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectInst
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectTick
