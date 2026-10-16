import InitECandidate.Solver.FlattenWeighted.CallTail
import InitECandidate.Solver.FlattenBound.CallReturn
import InitECandidate.Solver.FlattenBound.CallBudget
import InitECandidate.Solver.FlattenBound.Syntax

/-! Returning/exceptional calls preserve the exposed callee and continuation
clock witnesses, including return-label setup and the optional handler join. -/
namespace InitECandidate.Solver.FlattenWeighted
open Flapjack.Compiler.Backend
open InitECandidate.Solver.FlattenBound
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
section
variable {width : Nat} [NeZero width] {C F : Type}

/-- Unpacked `Vloc` conclusion. -/
theorem paidConclVloc (credits : Nat) {p : HolProg width} {t : Bool} {x : StackSemResult width}
    {s1 s2 : StackSemStateFiniteExact width C F} {n l : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F} {n1 n2 : Nat}
    (hh : haltView (some x) = none) (hr : resultView x n cs bs = .vloc n1 n2)
    (h : PaidConcl credits p s1 t (some x) s2 n l cs bs t1) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      ck ≤ 4 * credits ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      ∀ w, locToPc n1 n2 t2.code = some w → w = t2.pc ∧ stateRel s2 t2 := by
  obtain ⟨ck, t2, small, h⟩ := h
  refine ⟨ck, t2, small, ?_⟩
  revert h
  rw [hh]
  simp only [Option.map_some, hr]
  rintro ⟨a, b, c, d, e, f, g, -, w⟩
  exact ⟨a, b, c, d, e, f, g, w⟩

/-- Result propagation through a returning call (results other than a
matching return or a handled exception). -/
theorem paidCallPropagate (wholeCredit subCredit : Nat) {p p' : HolProg width} {t : Bool} {x : StackSemResult width}
    {s1 middle s2 : StackSemStateFiniteExact width C F} {d n l l' : Nat} {cs bs : List Nat}
    {t1 tE : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run1 : ∀ ck1, evaluate { t1 with clock := t1.clock + 1 + ck1 } =
      evaluate { tE with clock := tE.clock + ck1 })
    (f1 : tE.lenReg = t1.lenReg) (f2 : tE.ptrReg = t1.ptrReg) (f3 : tE.len2Reg = t1.len2Reg)
    (f4 : tE.ptr2Reg = t1.ptr2Reg) (f5 : tE.linkReg = t1.linkReg) (fcode : tE.code = t1.code)
    (hind : ∀ cs bs cs' bs' : List Nat, ∀ m m', resultView x m cs bs = resultView x m' cs' bs')
    (small : 1 + 4 * subCredit ≤ 4 * wholeCredit)
    (ph : PaidConcl subCredit p middle true (some x) s2 d l' [] [] tE) :
    PaidConcl wholeCredit p' s1 t (some x) s2 n l cs bs t1 :=
  paidConclComposeSome wholeCredit subCredit run1 f1 f2 f3 f4 f5 (by rw [fcode]; exact List.prefix_refl _) small
    (paidConclResult subCredit subCredit (p' := p) (t' := true) (l' := 0) (h := ph) (Nat.le_refl _) rfl (hind _ _ _ _ _ _))

/-- `Call` case with a return handler. -/
theorem paidCallRet (calleeCredit nextCredit : Nat) (s1 : StackSemStateFiniteExact width C F) (rp : HolProg width)
    (link l1 l2 : Nat) (dest : Nat ⊕ Nat) (handler : Option (HolProg width × Nat × Nat))
    (callee : s1.clock ≠ 0 → ∀ prog,
      StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code = some prog →
      PaidProp calleeCredit prog (StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)))
    (returned : ∀ prog post,
      StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code = some prog →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.result (.loc l1 l2)), post) →
      PaidProp nextCredit rp post)
    (raised : ∀ prog post hp hs hl, handler = some (hp, hs, hl) →
      StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code = some prog →
      StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
        (StackSemStateOps.setVar link (.loc l1 l2) s1)) = (some (.exception (.loc hs hl)), post) →
      PaidProp nextCredit hp post) :
    PaidProp (calleeCredit + nextCredit + 1) (.call (some (rp, link, l1, l2)) dest handler) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  unfold StackProps.callArgs at ca
  simp only at ca
  have caR := ca.1
  have caH := ca.2.2
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false rp n l cs bs with ⟨xs, nr1, m1⟩
  obtain ⟨rest, hflat, hrest⟩ := callRetPrelude (t := t) (link := link) (l1 := l1) (l2 := l2)
    (dest := dest) (handler := handler) h1
  have inst0 := inst
  rw [hflat] at inst
  obtain ⟨fetchA, inst2⟩ := lineAt rfl inst
  obtain ⟨fetchB, inst3⟩ := lineAt (Prelude.notIsLabelCompileJump dest) inst2
  obtain ⟨locL, inst4⟩ := labelAt inst3
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst4
  rcases hfind : StackSemControl.findCode dest (s1.regs.eraseEq link) s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, t1, Nat.zero_le _, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0] at ev
  obtain ⟨key, hlookup⟩ := findCode_mem dest (s1.regs.eraseEq link) s1.code prog hfind
  rcases e2 : StackSemEvaluate.evaluate (prog, StackSemStateOps.decClock
    (StackSemStateOps.setVar link (.loc l1 l2) s1)) with ⟨res0, s2'⟩
  have ev' := callRetEval e2 ev
  obtain ⟨d, pc', tE, run1, f1, f2, f3, f4, f5, fcode, fpc, relE, entry, caP, instP⟩ :=
    callEnter rel h0 fetchA fetchB (by simpa using locL) hfind
  have nerr0 : res0 ≠ some .error := by
    rintro rfl; exact err ev'
  have lt : MeasureLt prog (StackSemStateOps.decClock
      (StackSemStateOps.setVar link (.loc l1 l2) s1)) (.call (some (rp, link, l1, l2)) dest
        handler) s1 := .inl (setVarDecClockLt h0)
  have ph := callee h0 prog hfind true res0 s2' d (StackAlloc.nextLabHOL prog 2) [] [] tE
    ⟨e2, nerr0, relE, by rw [f1, f2, f3, f4, f5]; exact caP, by rw [fcode, fpc]; exact instP,
      by simp [fcode, entry]⟩
  have prop := fun (x : StackSemResult width) (hind : ∀ cs bs cs' bs' : List Nat, ∀ m m',
      resultView x m cs bs = resultView x m' cs' bs')
      (phx : PaidConcl calleeCredit prog
        (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) s1)) true (some x) s2' d (StackAlloc.nextLabHOL prog 2) [] [] tE) =>
    paidCallPropagate (calleeCredit + nextCredit + 1) calleeCredit (s1 := s1) (p' := .call (some (rp, link, l1, l2)) dest handler) (t := t) (n := n) (l := l)
      (cs := cs) (bs := bs) run1 f1 f2 f3 f4 f5 fcode hind
      (by omega) phx
  rcases res0 with _ | x
  · exact (err ev').elim
  rcases x with v | v | k | k | v | _ | o | _
  · -- the callee returned
    simp only at ev'
    by_cases hv : v = .loc l1 l2
    swap; · rw [if_pos hv] at ev'; exact (err ev').elim
    rw [if_neg (not_not.mpr hv)] at ev'
    subst hv
    obtain ⟨ck', t3, smallCall, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
      paidConclVloc calleeCredit (n1 := l1) (n2 := l2) rfl rfl ph
    rw [fcode] at pre3
    obtain ⟨hpc3, rel3⟩ := hw (t1.pc + 1 + 1) (locToPcIsPrefix _ _ _ _ _ ⟨locL, pre3⟩)
    have rh := returned prog s2' hfind e2 false r s2 n l cs bs t3
      ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caR,
        by rw [← hpc3, h1]; exact codeInstalledIsPrefix _ _ _ _ ⟨instXs, pre3⟩,
        fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
    have smallRun : 1 + ck' + 4 * nextCredit + 1 ≤
        4 * (calleeCredit + nextCredit + 1) := by omega
    have run13 := chainRun run1 run3
    rcases handler with _ | ⟨hp, hs, hl⟩
    · rw [hrest rfl] at hflat
      refine paidConclCompose (calleeCredit + nextCredit + 1) nextCredit run13 (by rw [g1, f1]) (by rw [g2, f2]) (by rw [g3, f3])
        (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ (by omega) rh
      rw [hflat, ← hpc3, h1]
      cases dest <;> simp [isLabelHOL, Flapjack.Compiler.Backend.StackToLab.compileJumpHOL] <;> omega
    · obtain ⟨ys, m2, fetchJ, locH, instYs, locEnd, total, -⟩ := callHandlerCode h1 inst0
      cases r with
      | some x =>
        exact paidConclComposeSome (calleeCredit + nextCredit + 1) nextCredit run13 (by rw [g1, f1]) (by rw [g2, f2])
          (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 (by omega) rh
      | none =>
        obtain ⟨ck2, t4, smallReturn, run4, k1, k2, k3, k4, k5, pre4, hpc4, rel4⟩ := paidConclNone nextCredit rh
        rw [h1] at hpc4
        have pre34 := pre3.trans pre4
        have fetchJ4 : asmFetchAux t4.pc t4.code =
            some (.labAsm (.jump (.lab n m2)) 0 [] 0) := by
          rw [hpc4, ← hpc3]; exact asmFetchAuxSomeIsPrefix _ _ _ _ ⟨fetchJ, pre34⟩
        have locEnd4 := locToPcIsPrefix _ _ _ _ _ ⟨locEnd, pre34⟩
        refine ⟨(1 + ck') + ck2 + 1, { t4 with pc := t1.pc + 1 + 1 +
            ((appListAppend xs).filter (fun x => !isLabelHOL x)).length + 1 +
            ((appListAppend ys).filter (fun x => !isLabelHOL x)).length }, (by omega), fun ck1 => ?_,
          by rw [k1, g1, f1], by rw [k2, g2, f2], by rw [k3, g3, f3], by rw [k4, g4, f4],
          by rw [k5, g5, f5], pre34, ?_, rel4⟩
        · rw [show t1.clock + ((1 + ck') + ck2 + 1) + ck1 =
              t1.clock + ((1 + ck') + ck2) + (ck1 + 1) by omega, chainRun run13 run4,
            show t4.clock + (ck1 + 1) = (t4.clock + ck1) + 1 by omega,
            jumpStep (t4.clock + ck1) fetchJ4 locEnd4]
        · simp only [total]; omega
  · -- the callee raised
    rcases handler with _ | ⟨hp, hs, hl⟩
    · simp only at ev'
      simp only [Prod.mk.injEq] at ev'
      obtain ⟨rfl, rfl⟩ := ev'
      exact prop _ (fun _ _ _ _ _ _ => by cases v <;> rfl) ph
    · simp only at ev'
      by_cases hv : v = .loc hs hl
      swap; · rw [if_pos hv] at ev'; exact (err ev').elim
      rw [if_neg (not_not.mpr hv)] at ev'
      subst hv
      obtain ⟨ys, m2, -, locH, instYs, -, total, h2⟩ := callHandlerCode h1 inst0
      obtain ⟨ck', t3, smallCall, run3, g1, g2, g3, g4, g5, pre3, hw⟩ :=
        paidConclVloc calleeCredit (n1 := hs) (n2 := hl) rfl rfl ph
      rw [fcode] at pre3
      obtain ⟨hpc3, rel3⟩ := hw _ (locToPcIsPrefix _ _ _ _ _ ⟨locH, pre3⟩)
      simp only at caH
      have rh := raised prog s2' hp hs hl rfl hfind e2 false r s2 n m1 cs bs t3
        ⟨ev', nerr, rel3, by rw [g1, g2, g3, g4, g5, f1, f2, f3, f4, f5]; exact caH,
          by rw [← hpc3, h2]; exact codeInstalledIsPrefix _ _ _ _ ⟨instYs, pre3⟩,
          fun k hk => isSomeLocToPcPrefix ⟨labs k hk, pre3⟩⟩
      have smallRun : 1 + ck' + 4 * nextCredit ≤
          4 * (calleeCredit + nextCredit + 1) := by omega
      refine paidConclCompose (calleeCredit + nextCredit + 1) nextCredit (chainRun run1 run3) (by rw [g1, f1]) (by rw [g2, f2])
        (by rw [g3, f3]) (by rw [g4, f4]) (by rw [g5, f5]) pre3 ?_ smallRun rh
      rw [total, ← hpc3, h2]
      omega
  · exact (err ev').elim
  · exact (err ev').elim
  all_goals
    simp only [Prod.mk.injEq] at ev'
    obtain ⟨rfl, rfl⟩ := ev'
    exact prop _ (fun _ _ _ _ _ _ => rfl) ph

end
end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.paidConclVloc
#print axioms InitECandidate.Solver.FlattenWeighted.paidCallPropagate
#print axioms InitECandidate.Solver.FlattenWeighted.paidCallRet
