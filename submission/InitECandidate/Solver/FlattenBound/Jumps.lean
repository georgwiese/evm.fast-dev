import InitECandidate.Solver.FlattenBound.Loop
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Jumps

/-! Bounded direct and raw procedure entry, with explicit callee-size and
bounded-callee-run premises. The source already charges the entry jump. -/
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
variable {width : Nat} [NeZero width] {C F : Type}

/-- `JumpLower` case. -/
theorem flattenCorrectJumpLower (limit : Nat) (s1 : StackSemStateFiniteExact width C F) (r1 r2 dest : Nat)
    (bodies : ∀ key prog, sptLookup key s1.code = some prog → nodes prog ≤ limit)
    (callee : s1.clock ≠ 0 → ∀ key prog, sptLookup key s1.code = some prog →
      BoundedProp limit prog (StackSemStateOps.decClock s1)) :
    BoundedProp limit (.jumpLower r1 r2 dest) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_jumpLower] at ev
  have fetch : asmFetchAux t1.pc t1.code =
      some (.labAsm (.jumpCmp .lower r1 (.reg r2) (.lab dest 0)) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  rcases hx : StackSemStateOps.getVar r1 s1 with _ | ⟨x | ⟨_, _⟩⟩ <;>
    rcases hy : StackSemStateOps.getVar r2 s1 with _ | ⟨y | ⟨_, _⟩⟩ <;>
    simp only [hx, hy] at ev <;> try exact (err ev).elim
  have hcmp : wordSemWordCmp .lower (t1.regs r1) (regImm (.reg r2) t1) =
      some (wordCmpHOL .lower x y) := by
    simp [regImm, InstCorrect.regOfLookup rel hx, InstCorrect.regOfLookup rel hy, wordSemWordCmp]
  have clk := relClock rel
  by_cases hlow : wordCmpHOL .lower x y = true
  · rw [if_pos hlow] at ev
    rw [hlow] at hcmp
    split at ev
    · exact (err ev).elim
    rename_i prog hfind
    have hlook : sptLookup dest s1.code = some prog := by
      simpa [StackSemControl.findCode] using hfind
    obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
    by_cases h0 : s1.clock = 0
    · rw [if_pos h0] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      refine ⟨0, t1, Nat.zero_le _, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
      · simp [StackSemStateOps.emptyEnv, relFfi rel]
      · omega
    · rw [if_neg h0] at ev
      rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock s1) with ⟨res, s'⟩
      rw [e2] at ev
      simp only at ev
      by_cases hbad : StackSemControl.badFunReturn res = true
      · rw [if_pos hbad] at ev; exact (err ev).elim
      rw [if_neg hbad] at ev
      simp only [Prod.mk.injEq] at ev
      obtain ⟨rfl, rfl⟩ := ev
      obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
      have rel' : stateRel (StackSemStateOps.decClock s1)
          { t1 with pc := pc', clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
      have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.jumpLower r1 r2 dest) s1 :=
        .inl (by simp [StackSemStateOps.decClock]; omega)
      have ph := callee h0 dest prog hlook true (some x') s' dest (StackAlloc.nextLabHOL prog 2) [] []
        { t1 with pc := pc', clock := t1.clock - 1 }
        ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
      have step := fun c => (jumpCmpStep (b := true) c fetch hcmp)
      simp only [if_true, entry] at step
      exact boundedConclComposeSome limit (runEnter (by omega) step) rfl rfl rfl rfl rfl
        (List.prefix_refl _)
        (by
          have finalClock := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
          simp only [StackSemStateOps.decClock] at finalClock ⊢
          have bound := budget_enter limit prog (.jumpLower r1 r2 dest) s1.clock s'.clock
            (budget limit prog (s1.clock - 1) s'.clock) (bodies dest prog hlook) h0
            finalClock (Nat.le_refl _)
          omega)
        (boundedConclResult limit (p' := prog) (t' := true) (l' := 0) (h := ph) (Nat.le_refl _) rfl
          (resultViewIndep hbad _ _ _ _ _ _))
  · have hlow' : wordCmpHOL .lower x y = false := by simpa using hlow
    rw [if_neg hlow] at ev
    rw [hlow'] at hcmp
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have step := fun c => (jumpCmpStep (b := false) c fetch hcmp)
    simp only [Bool.false_eq_true, if_false] at step
    refine ⟨1, { t1 with pc := t1.pc + 1 }, one_le_budget _ _ _ _, runToPc step, rfl, rfl, rfl, rfl, rfl,
      List.prefix_refl _, ?_, rel⟩
    simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList, isLabelHOL]

/-- `RawCall` case. -/
theorem flattenCorrectRawCall (limit : Nat) (s1 : StackSemStateFiniteExact width C F) (dest : Nat)
    (bodies : ∀ key prog, sptLookup key s1.code = some prog → nodes prog ≤ limit)
    (callee : s1.clock ≠ 0 → ∀ p body, sptLookup dest s1.code = some (.seq p body) →
      BoundedProp limit body (StackSemStateOps.decClock s1)) :
    BoundedProp limit (.rawCall dest) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_rawCall] at ev
  have fetch : asmFetchAux t1.pc t1.code = some (.labAsm (.jump (.lab dest 1)) 0 [] 0) :=
    fetchSingle rfl (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hlook : sptLookup dest s1.code with _ | prog
  · rw [hlook] at ev; exact (err ev).elim
  rw [hlook] at ev
  simp only at ev
  rcases prog with _ | _ | _ | _ | _ | _ | ⟨p1, body⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ |
    _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _
  all_goals try (simp only [StackSemControl.destSeq] at ev; exact (err ev).elim)
  simp only [StackSemControl.destSeq] at ev
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  simp only [StackProps.callArgs] at caP
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false p1 dest (StackAlloc.nextLabHOL (.seq p1 body) 2) [] [] with
    ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false body dest l1 [] [] with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL true (.seq p1 body) dest
      (StackAlloc.nextLabHOL (.seq p1 body) 2) [] []).1 =
      appListAppend xs ++ (.label dest 1 0 :: appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]; simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at instP
  obtain ⟨-, instRest⟩ := codeInstalledAppendImp _ _ _ _ instP
  obtain ⟨loc1, instYs⟩ := labelAt instRest
  set lenXs := ((appListAppend xs).filter (fun x => !isLabelHOL x)).length with hLenXs
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, t1, Nat.zero_le _, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  rcases e2 : StackSemEvaluate.evaluate (body, StackSemStateOps.decClock s1) with ⟨res, s'⟩
  rw [e2] at ev
  simp only at ev
  by_cases hbad : StackSemControl.badFunReturn res = true
  · rw [if_pos hbad] at ev; exact (err ev).elim
  rw [if_neg hbad] at ev
  simp only [Prod.mk.injEq] at ev
  obtain ⟨rfl, rfl⟩ := ev
  obtain ⟨x', rfl⟩ := notBadFunReturnImpSome _ hbad
  have rel' : stateRel (StackSemStateOps.decClock s1)
      { t1 with pc := pc' + lenXs, clock := t1.clock - 1 } := StateRel.stateRelDecClock rel
  have lt : MeasureLt body (StackSemStateOps.decClock s1) (.rawCall dest) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := callee h0 p1 body hlook false (some x') s' dest l1 [] []
    { t1 with pc := pc' + lenXs, clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP.2, by rw [h2]; exact instYs, by simp [entry]⟩
  have step := fun c => jumpStep c fetch loc1
  exact boundedConclComposeSome limit (runEnter (by omega) step) rfl rfl rfl rfl rfl
    (List.prefix_refl _)
    (by
      have finalClock := StackSemEvaluateClock.evaluateClock _ _ _ _ e2
      have small := bodies dest (.seq p1 body) hlook
      simp only [nodes] at small
      simp only [StackSemStateOps.decClock] at finalClock ⊢
      have bound := budget_enter limit body (.rawCall dest) s1.clock s'.clock
        (budget limit body (s1.clock - 1) s'.clock) (by omega) h0 finalClock (Nat.le_refl _)
      omega)
    (boundedConclResult limit (p' := body) (t' := false) (l' := 0) (h := ph) (Nat.le_refl _) rfl
      (resultViewIndep hbad _ _ _ _ _ _))

end
end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectJumpLower
#print axioms InitECandidate.Solver.FlattenBound.flattenCorrectRawCall
