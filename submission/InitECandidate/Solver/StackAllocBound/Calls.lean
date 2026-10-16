import InitECandidate.Solver.StackAllocBound.Control

/-! Zero-extra-clock call and jump simulations with explicit eligible code
and oracle invariants, including matching returns and exception handlers. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps Flapjack.StackSemMeasure
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions

variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

/-- The target's clock decrement at a call site with positive source clock. -/
theorem decClock_tgt (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (ck : Nat) (h0 : s.clock ≠ 0) :
    decClock (Tgt anything cr c s ck regs) = Tgt anything cr c (decClock s) ck regs :=
  res_clock anything cr c (decClock s) regs (by simp only [decClock]; omega)

theorem goal_jumpLower (s : StackSemStateFiniteExact width C F) (r1 r2 dest : Nat)
    (safe : eligible (width := width) (.jumpLower r1 r2 dest) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.jumpLower r1 r2 dest) s) : ZeroGoal anything cr (.jumpLower r1 r2 dest) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_jumpLower] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.jumpLower r1 r2 dest, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i x y hx hy
    have gx : ∀ ck, getVar r1 (Tgt anything cr c s ck regs) = some (.word x) :=
      fun _ => hpre.regs _ _ hx
    have gy : ∀ ck, getVar r2 (Tgt anything cr c s ck regs) = some (.word y) :=
      fun _ => hpre.regs _ _ hy
    split at h
    · rename_i hlt
      split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      rename_i prog hprog
      have hprog' : sptLookup dest s.code = some prog := hprog
      obtain ⟨hk, hap⟩ := hpre.code dest prog hprog'
      obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hprog', hk⟩
      have hf : StackSemControl.findCode (.inl dest) regs
          (sptFromAList (compile c (sptToAList s.code))) = some (comp m1 n1 prog).1 := hcl
      by_cases h0 : s.clock = 0
      · rw [if_pos h0] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun _ => ?_⟩
        · rw [evaluate_jumpLower, gx, gy]
          simp only [hlt, if_true]
          rw [hf]
          simp only [tgt_zero, h0, if_true]
          rfl
        · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
          exact Nat.two_pow_pos width
      · rw [if_neg h0] at h
        rcases h1 : evaluate (prog, decClock s) with ⟨res, s2⟩
        rw [h1] at h
        dsimp only at h
        have hres : res ≠ some .error := by
          rintro rfl
          simp [StackSemControl.badFunReturn] at h
          exact hr h.1.symm
        obtain ⟨ck, regs1, zero, he, hpost⟩ :=
          ih prog (decClock s) (callee_measure_lt prog _ s h0)
            (stateSafe.1 dest prog hprog') stateSafe res s2 n1 m1 c regs h1 hres hap
            hpre.decClock
        refine ⟨ck, regs1, zero, ?_, ?_⟩
        · rw [evaluate_jumpLower, gx, gy]
          simp only [hlt, if_true]
          rw [hf]
          dsimp only
          rw [if_neg (by show s.clock + ck ≠ 0; omega), decClock_tgt anything cr c s regs ck h0, he]
          dsimp only
          split at h
          · simp only [Prod.mk.injEq] at h
            exact absurd h.1.symm hr
          · rw [if_neg ‹_›]
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        · split at h
          · simp only [Prod.mk.injEq] at h
            exact absurd h.1.symm hr
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hpost
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
      rw [evaluate_jumpLower, gx, gy]
      dsimp only
      rw [if_neg ‹_›]
      rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_rawCall (s : StackSemStateFiniteExact width C F) (dest : Nat)
    (safe : eligible (width := width) (.rawCall dest) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.rawCall dest) s) : ZeroGoal anything cr (.rawCall dest) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_rawCall] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.rawCall dest, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨hk, hap⟩ := hpre.code dest prog hprog
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hprog, hk⟩
  split at h
  · rename_i p0 body hds
    cases prog with
    | seq a b =>
      simp only [StackSemControl.destSeq, Option.some.injEq, Prod.mk.injEq] at hds
      obtain ⟨rfl, rfl⟩ := hds
      have hap2 : allocArg b := hap.2
      have hcl' : ∀ ck, sptLookup dest (Tgt anything cr c s ck regs).code =
          some (.seq (comp m1 n1 a).1 (comp m1 (comp m1 n1 a).2 b).1) := fun _ => hcl
      by_cases h0 : s.clock = 0
      · rw [if_pos h0] at h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun _ => ?_⟩
        · rw [evaluate_rawCall, hcl']
          simp only [StackSemControl.destSeq, tgt_zero, h0, if_true]
          rfl
        · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
          exact Nat.two_pow_pos width
      · rw [if_neg h0] at h
        rcases h1 : evaluate (b, decClock s) with ⟨res, s2⟩
        rw [h1] at h
        dsimp only at h
        have hres : res ≠ some .error := by
          rintro rfl
          simp [StackSemControl.badFunReturn] at h
          exact hr h.1.symm
        obtain ⟨ck, regs1, zero, he, hpost⟩ :=
          ih b (decClock s) (callee_measure_lt b _ s h0)
            (Bool.and_eq_true_iff.mp (stateSafe.1 dest (.seq a b) hprog)).2 stateSafe res s2 (comp m1 n1 a).2 m1 c regs
            h1 hres hap2 hpre.decClock
        refine ⟨ck, regs1, zero, ?_, ?_⟩
        · rw [evaluate_rawCall, hcl']
          simp only [StackSemControl.destSeq]
          rw [if_neg (by show s.clock + ck ≠ 0; omega), decClock_tgt anything cr c s regs ck h0, he]
          dsimp only
          split at h
          · simp only [Prod.mk.injEq] at h
            exact absurd h.1.symm hr
          · rw [if_neg ‹_›]
            simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            rfl
        · split at h
          · simp only [Prod.mk.injEq] at h
            exact absurd h.1.symm hr
          · simp only [Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hpost
    | _ => simp [StackSemControl.destSeq] at hds
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

/-- The compiled handler of a returning call. -/
def compHandler (n m : Nat) : Option (HolProg width × Nat × Nat) → Option (HolProg width × Nat × Nat)
  | none => none
  | some (hp, k1, k2) => some ((comp n m hp).1, k1, k2)

theorem comp_callSome (n m : Nat) (retH : HolProg width) (link l1 l2 : Nat) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat)) :
    (comp n m (.call (some (retH, link, l1, l2)) dest handler)).1 =
      .call (some ((comp n m retH).1, link, l1, l2)) dest
        (compHandler n (comp n m retH).2 handler) := by
  rcases handler with _ | ⟨hp, k1, k2⟩ <;> rfl

theorem Pre.setVar {cr : CompileFn width C} {c : DataToWord.Config}
    {s : StackSemStateFiniteExact width C F} {regs : HolFiniteMapExact Nat (WordLocW width)}
    (h : Pre cr c s regs) (k : Nat) (v : WordLocW width) :
    Pre cr c (StackSemStateOps.setVar k v s) (regs.updateEq (k, v)) :=
  ⟨h.code, h.oracle, h.gcFun, h.useAlloc, h.stack, submap_fupdate_both h.regs, h.useStack, h.buf,
    h.compile⟩

/-- The target state of a returning call site: register `link` set, clock decremented. -/
theorem callSite_tgt (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (ck link : Nat) (v : WordLocW width)
    (h0 : s.clock ≠ 0) :
    decClock (StackSemStateOps.setVar link v (Tgt anything cr c s ck regs)) =
      Tgt anything cr c (decClock (StackSemStateOps.setVar link v s)) ck (regs.updateEq (link, v)) :=
  res_clock anything cr c (decClock (StackSemStateOps.setVar link v s)) (regs.updateEq (link, v))
    (k := s.clock + ck - 1) (ck := ck) (by show s.clock + ck - 1 = s.clock - 1 + ck; omega)

theorem measure_setVar_call (p : HolProg width) (s : StackSemStateFiniteExact width C F)
    (link : Nat) (v : WordLocW width) :
    stackSemMeasure p (StackSemStateOps.setVar link v s) = stackSemMeasure p s := by
  simp [stackSemMeasure, StackSemStateOps.setVar]

theorem goal_call_none (s : StackSemStateFiniteExact width C F) (dest : Sum Nat Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (safe : eligible (.call none dest handler) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.call none dest handler) s) :
    ZeroGoal anything cr (.call none dest handler) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_call] at h
  dsimp only at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.call none dest none, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨k, hk, hfeq⟩ := find_code_IMP_lookup (find_code_regs_SUBMAP ⟨hpre.regs, hprog⟩)
  obtain ⟨hgc, hap⟩ := hpre.code k prog hk
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hk, hgc⟩
  have hf : StackSemControl.findCode dest regs (sptFromAList (compile c (sptToAList s.code))) =
      some (comp m1 n1 prog).1 := by rw [hfeq]; exact hcl
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  by_cases h0 : s.clock = 0
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun _ => ?_⟩
    · rw [evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      simp only [tgt_zero, h0, if_true]
      rfl
    · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
      exact Nat.two_pow_pos width
  · rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at h
    rcases h1 : evaluate (prog, decClock s) with ⟨res, s2⟩
    rw [h1] at h
    dsimp only at h
    have hres : res ≠ some .error := by
      rintro rfl
      simp [StackSemControl.badFunReturn] at h
      exact hr h.1.symm
    obtain ⟨ck, regs1, zero, he, hpost⟩ :=
      ih prog (decClock s) (callee_measure_lt prog _ s h0)
        (stateSafe.1 k prog hk) stateSafe res s2 n1 m1 c regs h1 hres hap
        hpre.decClock
    refine ⟨ck, regs1, zero, ?_, ?_⟩
    · rw [evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      rw [if_neg (by show s.clock + ck ≠ 0; omega), StackSemEvaluateClock.fixClockEvaluate,
        decClock_tgt anything cr c s regs ck h0, he]
      dsimp only
      split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · rw [if_neg ‹_›]
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rfl
    · split at h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hpost

theorem goal_call_some (s : StackSemStateFiniteExact width C F) (retH : HolProg width)
    (link l1 l2 : Nat) (dest : Sum Nat Nat) (handler : Option (HolProg width × Nat × Nat))
    (safe : eligible (.call (some (retH, link, l1, l2)) dest handler) = true) (stateSafe : StateSafe s)
    (ih : ZeroIH anything cr (.call (some (retH, link, l1, l2)) dest handler) s) :
    ZeroGoal anything cr (.call (some (retH, link, l1, l2)) dest handler) s := by
  intro r t m n c regs h hr ha hpre
  unfold StackProps.allocArg at ha
  obtain ⟨haR, haH⟩ := ha
  replace haR : StackProps.allocArg retH := haR
  rw [evaluate_call] at h
  dsimp only at h
  rw [comp_callSome]
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i prog hprog
  obtain ⟨k, hk, hfeq⟩ :=
    find_code_IMP_lookup (find_code_regs_SUBMAP ⟨submap_domsub_both (c := link) hpre.regs, hprog⟩)
  obtain ⟨hgc, hap⟩ := hpre.code k prog hk
  obtain ⟨m1, n1, hcl⟩ := lookup_IMP_lookup_compile (c := c) ⟨hk, hgc⟩
  have hf : StackSemControl.findCode dest (regs.eraseEq link)
      (sptFromAList (compile c (sptToAList s.code))) = some (comp m1 n1 prog).1 := by
    rw [hfeq]; exact hcl
  by_cases h0 : s.clock = 0
  · rw [if_pos h0] at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun _ => ?_⟩
    · rw [evaluate_call]
      dsimp only
      rw [hf]
      dsimp only
      simp only [tgt_zero, h0, if_true]
      rfl
    · simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
      exact Nat.two_pow_pos width
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at h
  have h0' : (StackSemStateOps.setVar link (.loc l1 l2) s).clock ≠ 0 := h0
  rcases h1 : evaluate (prog, decClock (StackSemStateOps.setVar link (.loc l1 l2) s)) with ⟨res, s2⟩
  rw [h1] at h
  have hres : res ≠ some .error := by
    rintro rfl
    simp only [Prod.mk.injEq] at h
    exact hr h.1.symm
  have hmc : LexNat (stackSemMeasure prog (decClock (StackSemStateOps.setVar link (.loc l1 l2) s)))
      (stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s) := by
    have := callee_measure_lt prog (.call (some (retH, link, l1, l2)) dest handler) _ h0'
    rwa [measure_setVar_call] at this
  have hpreC := (Pre.setVar hpre link (.loc l1 l2)).decClock
  obtain ⟨ck1, regs1, zero1, he1, hsub1, hbuf1, hst1⟩ :=
    ih prog _ hmc (stateSafe.1 k prog hk) stateSafe res s2 n1 m1 c _ h1 hres hap hpreC
  have stateSafe2 : StateSafe s2 :=
    stateSafe_evaluate prog (decClock (StackSemStateOps.setVar link (.loc l1 l2) s)) s2 res stateSafe h1
  -- the target call site
  have hsite : ∀ ck, decClock (StackSemStateOps.setVar link (.loc l1 l2) (Tgt anything cr c s ck regs)) =
      Tgt anything cr c (decClock (StackSemStateOps.setVar link (.loc l1 l2) s)) ck
        (regs.updateEq (link, .loc l1 l2)) :=
    fun ck => callSite_tgt anything cr c s regs ck link _ h0
  have hcont : ∀ (q : HolProg width), LexNat (stackSemMeasure q s2)
      (stackSemMeasure (.call (some (retH, link, l1, l2)) dest handler) s) := by
    intro q
    have := call_continuation_measure_lt q (.call (some (retH, link, l1, l2)) dest handler) s link l1
      l2 (evaluate (prog, decClock (StackSemStateOps.setVar link (.loc l1 l2) s))) h0
    rwa [StackSemEvaluateClock.fixClockEvaluate, h1] at this
  -- the callee in the target, with `ck2` more clock when it does not time out
  have hcallee : ∀ ck2, (ck2 = 0 ∨ res ≠ some .timeOut) →
      evaluate ((comp m1 n1 prog).1, Tgt anything cr c (decClock (StackSemStateOps.setVar link
        (.loc l1 l2) s)) (ck1 + ck2) (regs.updateEq (link, .loc l1 l2))) =
        (res, Tgt anything cr c s2 ck2 regs1) := by
    rintro ck2 (rfl | hto)
    · exact he1
    · exact target_add_clock anything cr he1 hto ck2
  -- the continuation shape of the target evaluation
  have htgt : ∀ ck2, (ck2 = 0 ∨ res ≠ some .timeOut) →
      evaluate (.call (some ((comp n m retH).1, link, l1, l2)) dest
        (compHandler n (comp n m retH).2 handler), Tgt anything cr c s (ck1 + ck2) regs) =
      match (res, Tgt anything cr c s2 ck2 regs1) with
      | (some (.result x), s2) =>
          if x ≠ .loc l1 l2 then (some .error, s2) else evaluate ((comp n m retH).1, s2)
      | (some (.exception x), s2) =>
          match compHandler n (comp n m retH).2 handler with
          | none => (some (.exception x), s2)
          | some (h, hl1, hl2) =>
              if x ≠ .loc hl1 hl2 then (some .error, s2) else evaluate (h, s2)
      | (none, s2) => (some .error, s2)
      | (some (.break _), s2) => (some .error, s2)
      | (some (.continue _), s2) => (some .error, s2)
      | (res, s2) => (res, s2) := by
    intro ck2 hck
    rw [evaluate_call]
    dsimp only
    rw [hf]
    dsimp only
    rw [if_neg (by show s.clock + (ck1 + ck2) ≠ 0; omega), StackSemEvaluateClock.fixClockEvaluate,
      hsite, hcallee ck2 hck]
    rfl
  have hpre2 : ∀ x, res = some (.result x) ∨ res = some (.exception x) →
      Pre cr c s2 regs1 := by
    rintro x (rfl | rfl) <;> exact Pre.of_evaluate h1 hpreC hsub1 hbuf1 (hst1 (by simp))
  rcases res with _ | ⟨x | x | _ | _ | w | _ | ev | _⟩
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · -- Result
    dsimp only at h
    by_cases hx : x = .loc l1 l2
    · rw [if_neg (not_not.2 hx)] at h
      obtain ⟨ck2, regs2, zero2, he2, hpost2⟩ :=
        ih retH s2 (hcont retH) (eligible_return retH link l1 l2 dest handler safe) stateSafe2 r t m n c regs1 h hr haR (hpre2 x (Or.inl rfl))
      refine ⟨ck1 + ck2, regs2, (by omega), ?_, hpost2⟩
      rw [htgt ck2 (Or.inr (by simp))]
      dsimp only
      rw [if_neg (not_not.2 hx)]
      exact he2
    · rw [if_pos hx] at h
      simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · -- Exception
    dsimp only at h
    rcases handler with _ | ⟨hp, k1, k2⟩
    · simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨ck1, regs1, zero1, ?_, hsub1, hbuf1, hst1⟩
      have h00 := htgt 0 (Or.inl rfl)
      simp only [Nat.add_zero] at h00
      rw [h00]
      rfl
    · replace haH : StackProps.allocArg hp := haH
      dsimp only at h
      by_cases hx : x = .loc k1 k2
      · rw [if_neg (not_not.2 hx)] at h
        obtain ⟨ck2, regs2, zero2, he2, hpost2⟩ :=
          ih hp s2 (hcont hp)
            (eligible_handler (some (retH, link, l1, l2)) dest hp k1 k2 safe) stateSafe2 r t (comp n m retH).2 n c regs1 h hr haH (hpre2 x (Or.inr rfl))
        refine ⟨ck1 + ck2, regs2, (by omega), ?_, hpost2⟩
        rw [htgt ck2 (Or.inr (by simp))]
        dsimp only [compHandler]
        rw [if_neg (not_not.2 hx)]
        exact he2
      · rw [if_pos hx] at h
        simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  all_goals
    dsimp only at h
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨ck1, regs1, zero1, ?_, hsub1, hbuf1, hst1⟩
    have h00 := htgt 0 (Or.inl rfl)
    simp only [Nat.add_zero] at h00
    rw [h00]
    rfl

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.goal_jumpLower
#print axioms InitECandidate.Solver.StackAllocBound.goal_rawCall
#print axioms InitECandidate.Solver.StackAllocBound.goal_call_none
#print axioms InitECandidate.Solver.StackAllocBound.goal_call_some
