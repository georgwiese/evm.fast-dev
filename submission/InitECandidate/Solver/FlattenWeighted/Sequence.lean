import InitECandidate.Solver.FlattenWeighted.Common
import InitECandidate.Solver.FlattenBound.Control
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Control

/-! Composition retains the numerical witnesses and telescopes spent source
clock. The Seq rule assumes bounded simulations for its actual sub-runs. -/
namespace InitECandidate.Solver.FlattenWeighted
open Flapjack.Compiler.Backend
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
section
variable {width : Nat} [NeZero width] {C F : Type}

/-- The conclusion for a result does not depend on the program, tail flag
or next label. -/
theorem paidConclSome (firstCredit secondCredit : Nat) {p p' : HolProg width} {t t' : Bool} {x : StackSemResult width}
    {s1 s2 : StackSemStateFiniteExact width C F} {n l l' : Nat} {cs bs : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (size : firstCredit ≤ secondCredit)
    (h : PaidConcl firstCredit p s1 t (some x) s2 n l cs bs t1) :
    PaidConcl secondCredit p' s1 t' (some x) s2 n l' cs bs t1 := by
  obtain ⟨ck, t2, bounded, h⟩ := h
  refine ⟨ck, t2, ?_, ?_⟩
  · omega
  revert h
  cases haltView (some x) with
  | some res => exact id
  | none =>
    simp only [Option.map_some]
    cases resultView x n cs bs <;> exact id

/-- Composition of a LabSem prefix run reaching `t2` with the conclusion of a
following sub-program started in `t2`. -/
theorem paidConclCompose (wholeCredit subCredit : Nat) {p p' : HolProg width} {t t' : Bool}
    {r : Option (StackSemResult width)} {s1 middle s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (hlen : t1.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length =
      t2.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t' p' n l' cs bs).1).filter
        (fun x => !isLabelHOL x)).length)
    (small : ck + 4 * subCredit ≤ 4 * wholeCredit)
    (h : PaidConcl subCredit p' middle t' r s2 n l' cs bs t2) :
    PaidConcl wholeCredit p s1 t r s2 n l cs bs t1 := by
  obtain ⟨ck', t3, bounded, h⟩ := h
  refine ⟨ck + ck', t3, by omega, ?_⟩
  revert h
  cases haltView r with
  | some res =>
    rintro ⟨ev, ffi⟩
    refine ⟨?_, ffi⟩
    rw [← Nat.add_assoc, run ck', ev]
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      cases r.map (fun w => resultView w n cs bs) with
      | none => rintro ⟨hpc, rel⟩; exact ⟨by omega, rel⟩
      | some v => cases v <;> exact id

/-- Unpacked no-result conclusion of a sub-program. -/
theorem paidConclNone (limit : Nat) {p : HolProg width} {t : Bool} {s1 s2 : StackSemStateFiniteExact width C F}
    {n l : Nat} {cs bs : List Nat} {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (h : PaidConcl limit p s1 t none s2 n l cs bs t1) :
    ∃ (ck : Nat) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      ck ≤ 4 * limit ∧
      (∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
        evaluate { t2 with clock := t2.clock + ck1 }) ∧
      t2.lenReg = t1.lenReg ∧ t2.ptrReg = t1.ptrReg ∧ t2.len2Reg = t1.len2Reg ∧
      t2.ptr2Reg = t1.ptr2Reg ∧ t2.linkReg = t1.linkReg ∧ t1.code <+: t2.code ∧
      t2.pc = t1.pc + ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t p n l cs bs).1).filter
        (fun x => !isLabelHOL x)).length ∧ stateRel s2 t2 := h

/-- `Seq` case. -/
theorem paidSeq (firstCredit secondCredit : Nat) (s1 : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (first : PaidProp firstCredit c1 s1)
    (second : ∀ middle, StackSemEvaluate.evaluate (c1, s1) = (none, middle) →
      PaidProp secondCredit c2 middle) : PaidProp (firstCredit + secondCredit) (.seq c1 c2) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, ca, inst, labs⟩
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at ev
  simp only [StackProps.callArgs] at ca
  rcases h1 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c1 n l cs bs with ⟨xs, nr1, l1⟩
  rcases h2 : Flapjack.Compiler.Backend.StackToLab.flattenHOL false c2 n l1 cs bs with ⟨ys, nr2, l2⟩
  have hflat : appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.seq c1 c2) n l cs bs).1 =
      appListAppend xs ++ ((if t then [.label n 1 0] else []) ++ appListAppend ys) := by
    rw [Flapjack.Compiler.Backend.StackToLab.flattenHOL]
    cases t <;> simp [h1, h2, appListAppendAppend, appListAppendList]
  rw [hflat] at inst
  obtain ⟨instXs, instRest⟩ := codeInstalledAppendImp _ _ _ _ inst
  have instYs : codeInstalled (t1.pc + ((appListAppend xs).filter
      (fun x => !isLabelHOL x)).length) (appListAppend ys) t1.code := by
    cases t
    · simpa using instRest
    · simp only [if_true, List.singleton_append, codeInstalled_cons, isLabelHOL] at instRest
      exact instRest.2
  have lenFlat : ((appListAppend (Flapjack.Compiler.Backend.StackToLab.flattenHOL t (.seq c1 c2) n l cs bs).1).filter
      (fun x => !isLabelHOL x)).length =
      ((appListAppend xs).filter (fun x => !isLabelHOL x)).length +
        ((appListAppend ys).filter (fun x => !isLabelHOL x)).length := by
    rw [hflat]; cases t <;> simp [List.filter_append, isLabelHOL]
  rcases e1 : StackSemEvaluate.evaluate (c1, s1) with ⟨r1, s1'⟩
  rw [e1] at ev
  have lt1 : MeasureLt c1 s1 (.seq c1 c2) s1 :=
    .inr ⟨rfl, StackSemMeasure.seq_first_size_lt c1 c2⟩
  cases r1 with
  | some x =>
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    have := first false (some x) s1' n l cs bs t1
      ⟨e1, nerr, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    exact paidConclSome firstCredit (firstCredit + secondCredit) (by omega) this
  | none =>
    simp only at ev
    have c1h := first false none s1' n l cs bs t1
      ⟨e1, by simp, rel, ca.1, by rw [h1]; exact instXs, labs⟩
    obtain ⟨ck, t2, bounded, run, f1, f2, f3, f4, f5, pre, hpc, rel2⟩ := paidConclNone firstCredit c1h
    rw [h1] at hpc
    have lt2 : MeasureLt c2 s1' (.seq c1 c2) s1 :=
      measureLtOfClockLe (StackSemEvaluateClock.evaluateClock _ _ _ _ e1)
        (StackSemMeasure.seq_second_size_lt c1 c2)
    have c2h := second s1' e1 false r s2 n l1 cs bs t2
      (flattenHypsMid ev nerr rel2 ca.2 f1 f2 f3 f4 f5 pre
        (by rw [h2, hpc]; exact instYs) labs)
    refine paidConclCompose (firstCredit + secondCredit) secondCredit run f1 f2 f3 f4 f5 pre ?_ ?_ c2h
    swap
    · omega
    simp only [lenFlat, hpc, h2]
    omega

end
end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.paidConclCompose
#print axioms InitECandidate.Solver.FlattenWeighted.paidSeq
