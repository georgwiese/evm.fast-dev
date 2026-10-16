import InitECandidate.Solver.StackAllocBound.Leaves
import InitECandidate.Solver.StackAllocBound.Safety
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Control

/-! Zero-clock composition for allocation lowering, with guarded induction
hypotheses over the explicitly eligible program and code/oracle class. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

/-- The induction hypothesis: `comp_correct` for every smaller program/state. -/
abbrev ZeroIH (p : HolProg width) (s : StackSemStateFiniteExact width C F) : Prop :=
  ∀ (q : HolProg width) (u : StackSemStateFiniteExact width C F),
    LexNat (stackSemMeasure q u) (stackSemMeasure p s) →
    eligible q = true → StateSafe u → ZeroGoal anything cr q u

theorem res_clock (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) {k ck : Nat} (h : k = s.clock + ck) :
    { Res anything cr c s regs with clock := k } = Tgt anything cr c s ck regs := by
  subst h; rfl

theorem tgt_add (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (ck1 ck2 : Nat) :
    Tgt anything cr c s (ck1 + ck2) regs =
      { Tgt anything cr c s ck1 regs with clock := (Tgt anything cr c s ck1 regs).clock + ck2 } := by
  show { Res anything cr c s regs with clock := s.clock + (ck1 + ck2) } =
    { Res anything cr c s regs with clock := s.clock + ck1 + ck2 }
  rw [Nat.add_assoc]

/-- The target run of a source evaluation, with `ck2` more clock (HOL's
`evaluate_add_clock` step). -/
theorem target_add_clock {c : DataToWord.Config} {q : HolProg width}
    {s t : StackSemStateFiniteExact width C F} {regs regs1 : HolFiniteMapExact Nat (WordLocW width)}
    {r : Option (StackSemResult width)} {ck1 : Nat}
    (he : evaluate (q, Tgt anything cr c s ck1 regs) = (r, Res anything cr c t regs1))
    (hr : r ≠ some .timeOut) (ck2 : Nat) :
    evaluate (q, Tgt anything cr c s (ck1 + ck2) regs) = (r, Tgt anything cr c t ck2 regs1) := by
  rw [tgt_add, evaluateAddClock ck2 _ _ _ _ ⟨he, hr⟩]

theorem Pre.decClock {cr : CompileFn width C} {c : DataToWord.Config}
    {s : StackSemStateFiniteExact width C F} {regs : HolFiniteMapExact Nat (WordLocW width)}
    (h : Pre cr c s regs) : Pre cr c (decClock s) regs :=
  ⟨h.code, h.oracle, h.gcFun, h.useAlloc, h.stack, h.regs, h.useStack, h.buf, h.compile⟩

theorem goal_seq (s : StackSemStateFiniteExact width C F) (c1 c2 : HolProg width)
    (safe : eligible (.seq c1 c2) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.seq c1 c2) s) : ZeroGoal anything cr (.seq c1 c2) s := by
  intro r t m n c regs h hr ha hpre
  obtain ⟨ha1, ha2⟩ := ha
  rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate] at h
  rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
  rw [h1] at h
  have hr1 : r1 ≠ some .error := by
    rintro rfl; simp only [Prod.mk.injEq] at h; exact hr h.1.symm
  obtain ⟨ck1, regs1, zero1, he1, hsub1, hbuf1, hst1⟩ :=
    ih c1 s (seq_first_measure_lt c1 c2 s) (Bool.and_eq_true_iff.mp safe).1 stateSafe r1 t1 m n c regs h1 hr1 ha1 hpre
  show ∃ ck regs1, ck = 0 ∧ evaluate (.seq (comp n m c1).1 (comp n (comp n m c1).2 c2).1,
    Tgt anything cr c s ck regs) = _ ∧ _
  cases r1 with
  | some x =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, regs1, zero1, ?_, hsub1, hbuf1, hst1⟩
      rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, he1]
  | none =>
      have hm := seq_second_measure_lt c1 c2 s (evaluate (c1, s))
      rw [StackSemEvaluateClock.fixClockEvaluate, h1] at hm
      have hpre1 := Pre.of_evaluate h1 hpre hsub1 hbuf1 (hst1 (by simp))
      obtain ⟨ck2, regs2, zero2, he2, hpost2⟩ :=
        ih c2 t1 hm (Bool.and_eq_true_iff.mp safe).2
          (stateSafe_evaluate c1 s t1 none stateSafe h1) r t (comp n m c1).2 n c regs1 h hr ha2 hpre1
      refine ⟨ck1 + ck2, regs2, (by omega), ?_, hpost2⟩
      rw [evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
        target_add_clock anything cr he1 (by simp) ck2]
      exact he2

theorem getVarImm_res (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (hsub : s.regs.submap regs)
    (ri : Compiler.Encoders.Asm.HolRegImm width) {y : WordLocW width}
    (h : StackSemStateOps.getVarImm ri.toWordRegImm s = some y) :
    StackSemStateOps.getVarImm ri.toWordRegImm (Res anything cr c s regs) = some y := by
  cases ri with
  | reg k => exact hsub _ _ h
  | imm w => exact h

theorem goal_ite (s : StackSemStateFiniteExact width C F) (cmp : Compiler.Encoders.Asm.HolCmp)
    (r1 : Nat) (ri : Compiler.Encoders.Asm.HolRegImm width) (c1 c2 : HolProg width)
    (safe : eligible (.ite cmp r1 ri c1 c2) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.ite cmp r1 ri c1 c2) s) : ZeroGoal anything cr (.ite cmp r1 ri c1 c2) s := by
  intro r t m n c regs h hr ha hpre
  obtain ⟨ha1, ha2⟩ := ha
  rw [evaluate_ite] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.ite cmp r1 ri (comp n m c1).1 (comp n (comp n m c1).2 c2).1,
    Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i x y hx hy
    split at h
    · rename_i hc
      obtain ⟨ck, regs1, zero, he, hpost⟩ :=
        ih c1 s (if_first_measure_lt cmp r1 ri c1 c2 s) (Bool.and_eq_true_iff.mp safe).1 stateSafe r t m n c regs h hr ha1 hpre
      refine ⟨ck, regs1, zero, ?_, hpost⟩
      rw [evaluate_ite, tgt_eq]
      rw [show getVar r1 { Res anything cr c s regs with clock := s.clock + ck } = some x from
          getVar_res anything cr c s regs hpre.regs hx,
        show StackSemStateOps.getVarImm ri.toWordRegImm { Res anything cr c s regs with clock := s.clock + ck } =
          some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
      simp only [hc]
      exact he
    · rename_i hc
      obtain ⟨ck, regs1, zero, he, hpost⟩ :=
        ih c2 s (if_second_measure_lt cmp r1 ri c1 c2 s) (Bool.and_eq_true_iff.mp safe).2 stateSafe r t (comp n m c1).2 n c regs h hr ha2 hpre
      refine ⟨ck, regs1, zero, ?_, hpost⟩
      rw [evaluate_ite, tgt_eq]
      rw [show getVar r1 { Res anything cr c s regs with clock := s.clock + ck } = some x from
          getVar_res anything cr c s regs hpre.regs hx,
        show StackSemStateOps.getVarImm ri.toWordRegImm { Res anything cr c s regs with clock := s.clock + ck } =
          some y from getVarImm_res anything cr c s regs hpre.regs ri hy]
      simp only [hc]
      exact he
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem exitLoop_halt {res : Option (StackSemResult width)} (w : WordLocW width)
    (h : StackSemControl.exitLoop res = some (.halt w)) : res = some (.halt w) := by
  rcases res with _ | ⟨_ | _ | _ | _ | _ | _ | _ | _ | _⟩ <;>
    simp_all [StackSemControl.exitLoop]

theorem goal_loop (s : StackSemStateFiniteExact width C F) (c1 : HolProg width)
    (safe : eligible (.loop c1) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.loop c1) s) : ZeroGoal anything cr (.loop c1) s := by
  intro r t m n c regs h hr ha hpre
  rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate] at h
  rcases h1 : evaluate (c1, s) with ⟨r1, t1⟩
  rw [h1] at h
  dsimp only at h
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [StackSemControl.contLoop, StackSemControl.exitLoop] at h
    exact hr h.1.symm
  obtain ⟨ck1, regs1, zero1, he1, hsub1, hbuf1, hst1⟩ :=
    ih c1 s (loop_body_measure_lt c1 s) safe stateSafe r1 t1 m n c regs h1 hr1 ha hpre
  show ∃ ck regs1, ck = 0 ∧ evaluate (.loop (comp n m c1).1, Tgt anything cr c s ck regs) = _ ∧ _
  by_cases hl : StackSemControl.contLoop r1 = true
  · have hnh : ∀ w, r1 ≠ some (.halt w) := by
      rcases contLoopImp r1 hl with rfl | rfl <;> simp
    have hnt : r1 ≠ some .timeOut := by
      rcases contLoopImp r1 hl with rfl | rfl <;> simp
    rw [if_pos hl] at h
    by_cases h0 : t1.clock = 0
    · rw [if_pos h0] at h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, HolFiniteMapExact.empty, zero1, ?_, submap_empty _, hbuf1, fun _ => ?_⟩
      · rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
        dsimp only
        rw [if_pos hl, if_pos h0]
        rfl
      · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
        exact Nat.two_pow_pos width
    · rw [if_neg h0] at h
      have hm := loop_reentry_measure_lt c1 s (evaluate (c1, s))
      rw [StackSemEvaluateClock.fixClockEvaluate, h1] at hm
      have hpre1 := (Pre.of_evaluate h1 hpre hsub1 hbuf1 (hst1 hnh)).decClock
      obtain ⟨ck2, regs2, zero2, he2, hpost2⟩ :=
        ih (.loop c1) (decClock t1) (hm h0) safe
          (stateSafe_evaluate c1 s t1 r1 stateSafe h1) r t m n c regs1 h hr ha hpre1
      refine ⟨ck1 + ck2, regs2, (by omega), ?_, hpost2⟩
      rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate,
        target_add_clock anything cr he1 hnt ck2]
      dsimp only
      rw [if_pos hl, if_neg (by show t1.clock + ck2 ≠ 0; omega)]
      rw [show decClock (Tgt anything cr c t1 ck2 regs1) = Tgt anything cr c (decClock t1) ck2 regs1
        from res_clock anything cr c (decClock t1) regs1 (by simp [decClock]; omega)]
      exact he2
  · rw [if_neg hl] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ck1, regs1, zero1, ?_, hsub1, hbuf1, fun hh => hst1 fun w hw => hh w ?_⟩
    · rw [evaluate_loop, StackSemEvaluateClock.fixClockEvaluate, he1]
      dsimp only
      rw [if_neg hl]
    · rw [hw]; rfl

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.goal_seq
#print axioms InitECandidate.Solver.StackAllocBound.goal_ite
#print axioms InitECandidate.Solver.StackAllocBound.goal_loop
