import InitECandidate.Solver.CrepToLoopBound.LoopBudget
import InitECandidate.Solver.CrepToLoopBound.ExpressionSimulation
import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect

namespace InitECandidate.Solver.CrepToLoopBound
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

section LoopStep


variable {width : Nat} [NeZero width] {F : Type}

private theorem loop_step_cut_some {L L' : NumSet} {B : HolLoopProg width}
    {X Y : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (some r, Y)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (some r, Y) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h => rw [hc] at h; simp at h
  next h => exact hc

private theorem loop_step_none {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (none, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_continue {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.continue 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_break {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.break 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.cutRes L' (none, s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

private theorem loop_step_exit {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hr0 : r ≠ .continue 0) (hr1 : r ≠ .break 0)
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some r, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (LoopSemStateFiniteExact.exitLoop (some r), s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

end LoopStep

section WhileHelpers


variable {width : Nat} [NeZero width] {F : Type}

private theorem locals_rel_inter (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l sl tl) :
    crepToLoopLocalsRelExact ctxt l sl (sptInter tl l) := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter tl l)).isSome
    rw [sptLookup_sptInter, if_pos hk']
    exact h.2.2.1 k hk
  · obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hnl : (sptLookup n l).isSome := hn2
    refine ⟨n, hn1, hn2, ?_⟩
    show sptLookup n (sptInter tl l) = _
    rw [sptLookup_sptInter, if_pos hnl]
    exact hn3


private theorem locals_rel_insert_of (ctxt : CrepToLoopContextExact) (l nl : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl tl' : Spt (WordLocW width))
    (hl : crepToLoopLocalsRelExact ctxt l sl tl) (h1l : crepToLoopLocalsRelExact ctxt nl sl tl')
    (hsub : ∀ k, sptDomain l k → sptDomain nl k) (tmp : Nat) (htmp : ctxt.vmax < tmp)
    (x : WordLocW width) :
    crepToLoopLocalsRelExact ctxt l sl (sptInsert tmp x tl') := by
  refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hsub k hk)))
  · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
    obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
    have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
    subst hnn
    have hle := h1l.2.1 vn n' hn1'
    refine ⟨n', hn1', hn2, ?_⟩
    rw [sptLookup_sptInsert, if_neg (by omega)]
    exact hn3'

private theorem seq_continue_none {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F}
    (h : LoopSemStateFiniteExact.evaluate cC S = (none, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some (.continue 0), s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]
  simp only [LoopSemStateFiniteExact.evaluate]

private theorem seq_continue_some {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F} {x : LoopSemStateFiniteExact.LoopResultExact width}
    (h : LoopSemStateFiniteExact.evaluate cC S = (some x, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some x, s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]


private theorem while_body_eval (np : List (HolLoopProg width)) (le : HolLoopExp width)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg width) (Y st : LoopSemStateFiniteExact width F)
    (w : BitVec width) (h1 : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w)) :
    LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width)) (.seq cC (.continue 0)) (.break 0) l])) Y =
      if w = 0 then (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word w) st)
      else LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0))
          (LoopSemStateFiniteExact.setVar tmp (.word w) st)) := by
  generalize (HolLoopProg.seq cC (.continue 0) : HolLoopProg width) = q
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ h1]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
  simp only [LoopSemStateFiniteExact.evaluate, h1v]
  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
    LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rfl
  · have hb : (w == 0) = false := by simpa using hw
    simp only [hb, Bool.not_false, if_true, hw, if_false]
    split <;> rename_i h <;> exact h.symm

private theorem resultToLoop_exitLoop (r : CrepResultHOLExact width)
    (h0 : r ≠ .continue 0) (h1 : r ≠ .break 0) :
    LoopSemStateFiniteExact.exitLoop (resultToLoop (some r)) =
      resultToLoop (exitLoopCrepResult (some r)) := by
  cases r with
  | «continue» n => cases n with
    | zero => exact absurd rfl h0
    | succ n => rfl
  | «break» n => cases n with
    | zero => exact absurd rfl h1
    | succ n => rfl
  | _ => rfl

private theorem localsResultRel_exitLoop (ctxt : CrepToLoopContextExact) (l : NumSet)
    (s : CrepSemHOLState width F) (tt : LoopSemStateFiniteExact width F)
    (r : CrepResultHOLExact width) (h : localsResultRel ctxt l (some r) s tt) :
    localsResultRel ctxt l (exitLoopCrepResult (some r)) s tt := by
  cases r <;> exact h

end WhileHelpers

theorem simulateWhile {width : Nat} [NeZero width] {σ : Type} (limit : Nat) :
    ∀ (e : CrepExpHOL width) (c : CrepProgHOL width) (v1 : CrepSemHOLState width σ),
      CodeSafe limit v1.code → ceiling (.while e c) ≤ limit →
      (∀ (w : BitVec width) (res : Option (CrepResultHOLExact width))
          (s1 : CrepSemHOLState width σ),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 ∧
          evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (res, s1) ∧
          res = some (.continue 0) →
        Simulation limit (.while e c) s1) →
      (∀ (w : BitVec width) (res : Option (CrepResultHOLExact width))
          (s1 : CrepSemHOLState width σ),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 ∧
          evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (res, s1) ∧ res = none →
        Simulation limit (.while e c) s1) →
      (∀ (w : BitVec width),
        evalCrepSemHOLExp v1 e = some (.word w) ∧ w ≠ 0 ∧ v1.clock ≠ 0 →
        Simulation limit c (decClockCrepSemHOL v1)) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.while e c) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        ck ≤ (2 * limit + 3) * (v1.clock - s1.clock) + cost (.while e c) ∧
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.while e c))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 := by
  intro e c v1 safe bounded ihc ihn ihb res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  have bodyCeiling : ceiling c ≤ limit := by
    rw [ceiling] at bounded
    omega
  have localBound : expCost e + cost c ≤ 2 * limit + 3 := by
    have first := Nat.le_trans (cost_le_ceiling (.while e c)) bounded
    have second := Nat.le_trans (cost_le_ceiling c) bodyCeiling
    simp only [cost] at first
    omega
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
    simp only [hev, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word w =>
  simp only [hev] at he
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  have hlnl : ∀ k, sptDomain l k → sptDomain nl k :=
    fun k hk => hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
  have htmp : ctxt.vmax < tmp := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htA
  let B : HolLoopProg width := loopNestedSeqHOL (np ++
    [.assign tmp le,
     .ite .notEqual tmp (.imm (0 : BitVec width))
       (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])
  have hcomp : compileHOLExact ctxt l (.while e c) = .loop l B l := by
    rw [compileHOLExact, hC]
  rw [hcomp]
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  by_cases hw : w = 0
  · -- False case
    subst hw
    simp only [ne_eq, not_true_eq_false, if_false, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    obtain ⟨ck, st, prefixBudget, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
      expressionSimulation v1 e (.word 0) { t with locals := sptInter t.locals l }
        ctxt (ctxt.vmax + 1) l np le tmp nl
        ⟨hev, hs, hm, hg, hc, locals_rel_inter ctxt l v1.locals t.locals hl, hC,
          Nat.lt_succ_self _⟩
    have hentry : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + (ck + 2) }) =
        (none, { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + 2) } hsub]
      simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + 2) = 0 by omega, if_false]
      simp only [Prod.mk.injEq, true_and]
      congr 1
    have h1' : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
        { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) } =
          (none, { st with clock := st.clock + 1 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h1 (by simp)
      simpa [Nat.add_assoc] using this
    have hbody := while_body_eval np le tmp l (compileHOLExact ctxt l c) _ _ 0 h1'
      (by rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v)
    rw [if_pos rfl] at hbody
    have hloop := loop_step_break (L' := l) hentry hbody
    have hS : LoopSemStateFiniteExact.sptSubsetLive l
        (LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }).locals :=
      fun k hk => (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hlnl k hk)))
    have hexit : LoopSemStateFiniteExact.cutRes l
        (none, LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }) =
        (none, { st with locals := sptInter (sptInsert tmp (.word 0) st.locals) l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l _ hS]
      simp [LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.setVar]
    refine ⟨ck + 2, none, _, by simp only [cost]; omega, hloop.trans hexit, h1s, h1m, h1g, h1c, rfl, ?_⟩
    exact locals_rel_inter ctxt l v1.locals _
      (locals_rel_insert_of ctxt l nl v1.locals _ st.locals hl h1l hlnl tmp htmp _)
  · simp only [ne_eq, hw, not_false_eq_true, if_true] at he
    by_cases hz : v1.clock = 0
    · -- Timeout case
      simp only [hz, if_true, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have ht0 : t.clock = 0 := hs.2.2.1 ▸ hz
      have hcut : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + 0 }) =
          (some .timeOut, { t with clock := t.clock + 0, locals := .ln }) := by
        rw [LoopSemStateFiniteExact.cutRes]
        simp only
        rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + 0 } hsub]
        simp [ht0]
      exact ⟨0, some .timeOut, _, Nat.zero_le _, loop_step_cut_some hcut, hs, hm, hg, hc, rfl, trivial⟩
    · simp only [hz, if_false] at he
      rcases hbodyS : evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c with ⟨res', s1'⟩
      simp only [hbodyS] at he
      obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
      have htz : t.clock ≠ 0 := hs3 ▸ hz
      have hev' : evalCrepSemHOLExp (decClockCrepSemHOL v1) e = some (.word w) := by
        simp only [decClockCrepSemHOL, evalCrepSemHOLExp_upd_clock_eq, hev]
      have hsD : crepToLoopStateRelExact (decClockCrepSemHOL v1)
          { t with locals := sptInter t.locals l, clock := t.clock - 1 } :=
        ⟨hs1, hs2, by simp [decClockCrepSemHOL, hs3], hs4, hs5, hs6, hs7⟩
      obtain ⟨ck, st, prefixBudget, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
        expressionSimulation (decClockCrepSemHOL v1) e (.word w)
          { t with locals := sptInter t.locals l, clock := t.clock - 1 }
          ctxt (ctxt.vmax + 1) l np le tmp nl
          ⟨hev', hsD, hm, hg, hc, locals_rel_inter ctxt l v1.locals t.locals hl, hC,
            Nat.lt_succ_self _⟩
      have hne' : res' ≠ some .error := by
        rintro rfl
        simp only [exitLoopCrepResult, Prod.mk.injEq] at he
        exact hne he.1.symm
      obtain ⟨ck', res1', t1, bodyBudget, h2, h2s, h2m, h2g, h2c, h2r, h2l⟩ :=
        ihb w ⟨hev, hw, hz⟩ safe bodyCeiling res' s1' (LoopSemStateFiniteExact.setVar tmp (.word w) st) ctxt l
          hbodyS hne' h1s h1m h1g h1c (locals_rel_insert_of ctxt l nl v1.locals _ st.locals (locals_rel_inter ctxt l v1.locals t.locals hl) h1l hlnl tmp htmp _)
      have bodyDecrease : s1'.clock ≤ v1.clock - 1 := by
        simpa only [decClockCrepSemHOL] using clockDecrease hbodyS
      change ck' ≤ (2 * limit + 3) * ((v1.clock - 1) - s1'.clock) + cost c at bodyBudget
      have paid := prefixConsumeBudget (2 * limit + 3) v1.clock s1'.clock ck ck'
        (expCost e) (cost c) hz bodyDecrease prefixBudget bodyBudget localBound
      -- the loop entry, condition and body run from any clock extension
      have hentryK : ∀ k, LoopSemStateFiniteExact.cutRes l
          (none, { t with clock := t.clock + (ck + k) }) =
          (none, { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) }) := by
        intro k
        rw [LoopSemStateFiniteExact.cutRes]
        simp only
        rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + k) } hsub]
        simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + k) = 0 by omega, if_false]
        simp only [Prod.mk.injEq, true_and]
        congr 1
        omega
      have hbodyK : ∀ k, LoopSemStateFiniteExact.evaluate B
          { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) } =
          LoopSemStateFiniteExact.cutRes l
            (LoopSemStateFiniteExact.evaluate (.seq (compileHOLExact ctxt l c) (.continue 0))
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + k }) := by
        intro k
        have h1k : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
            { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) } =
              (none, { st with clock := st.clock + k }) := by
          have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
          simpa [Nat.add_assoc] using this
        have := while_body_eval np le tmp l (compileHOLExact ctxt l c) _ _ w h1k
          (by rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v)
        rw [if_neg hw] at this
        exact this
      have h2' : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
          { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + ck' } =
            (res1', t1) := h2
      cases res' with
      | none =>
        have hr1 : res1' = none := by simpa [resultToLoop] using h2r
        subst hr1
        obtain ⟨ck'', res1, t2, tailBudget, h3, h3s, h3m, h3g, h3c, h3r, h3l⟩ :=
          ihn w none s1' ⟨hev, hw, hz, hbodyS, rfl⟩ (codeSafe_evaluate (source := decClockCrepSemHOL v1) safe hbodyS) bounded res s1 t1 ctxt l
            he hne h2s h2m h2g h2c h2l
        rw [hcomp] at h3
        have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
            { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + ck'') } =
              (none, { t1 with clock := t1.clock + ck'' }) := by
          have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck'' h2' (by simp)
          simpa [Nat.add_assoc] using this
        have hb : LoopSemStateFiniteExact.evaluate B
            { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + ck'')) } =
            (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
          rw [hbodyK, seq_continue_none h2k]; rfl
        exact ⟨ck + (ck' + ck''), res1, t2,
          recursiveBudget (2 * limit + 3) v1.clock s1'.clock s1.clock ck ck' ck''
            (expCost e) (cost c) (cost (.while e c)) hz bodyDecrease (clockDecrease he)
            prefixBudget bodyBudget tailBudget localBound, (loop_step_continue (hentryK _) hb).trans h3,
          h3s, h3m, h3g, h3c, h3r, h3l⟩
      | some r =>
        by_cases hr0 : r = .continue 0
        · subst hr0
          simp only at he
          have hr1 : res1' = some (.continue 0) := by simpa [resultToLoop] using h2r
          subst hr1
          obtain ⟨ck'', res1, t2, tailBudget, h3, h3s, h3m, h3g, h3c, h3r, h3l⟩ :=
            ihc w (some (.continue 0)) s1' ⟨hev, hw, hz, hbodyS, rfl⟩ (codeSafe_evaluate (source := decClockCrepSemHOL v1) safe hbodyS) bounded res s1 t1 ctxt l
              he hne h2s h2m h2g h2c h2l
          rw [hcomp] at h3
          have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with
                  clock := st.clock + (ck' + ck'') } =
                (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
            have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ ck'' h2' (by simp)
            simpa [Nat.add_assoc] using this
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + ck'')) } =
              (some (.continue 0), { t1 with clock := t1.clock + ck'' }) := by
            rw [hbodyK, seq_continue_some h2k]; rfl
          exact ⟨ck + (ck' + ck''), res1, t2,
          recursiveBudget (2 * limit + 3) v1.clock s1'.clock s1.clock ck ck' ck''
            (expCost e) (cost c) (cost (.while e c)) hz bodyDecrease (clockDecrease he)
            prefixBudget bodyBudget tailBudget localBound, (loop_step_continue (hentryK _) hb).trans h3,
            h3s, h3m, h3g, h3c, h3r, h3l⟩
        by_cases hr1 : r = .break 0
        · subst hr1
          simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          have hr : res1' = some (.break 0) := by simpa [resultToLoop] using h2r
          subst hr
          have h2l' : crepToLoopLocalsRelExact ctxt l s1'.locals t1.locals := h2l
          have h2k : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l c)
              { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + 1) } =
                (some (.break 0), { t1 with clock := t1.clock + 1 }) := by
            have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2' (by simp)
            simpa [Nat.add_assoc] using this
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + (ck' + 1)) } =
              (some (.break 0), { t1 with clock := t1.clock + 1 }) := by
            rw [hbodyK, seq_continue_some h2k]; rfl
          have hsub1 : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
          have hexit : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
              (none, { t1 with locals := sptInter t1.locals l }) := by
            rw [LoopSemStateFiniteExact.cutRes]
            simp only
            rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub1]
            simp [LoopSemStateFiniteExact.decClock]
          exact ⟨ck + (ck' + 1), none, _, by simp only [cost]; omega, (loop_step_break (hentryK _) hb).trans hexit,
            h2s, h2m, h2g, h2c, rfl, locals_rel_inter ctxt l s1'.locals t1.locals h2l'⟩
        · have he' : (exitLoopCrepResult (some r), s1') = (res, s1) := by
            cases r with
            | «continue» n => cases n with
              | zero => exact absurd rfl hr0
              | succ n => exact he
            | «break» n => cases n with
              | zero => exact absurd rfl hr1
              | succ n => exact he
            | _ => exact he
          simp only [Prod.mk.injEq] at he'
          obtain ⟨rfl, rfl⟩ := he'
          obtain ⟨x, hx⟩ : ∃ x, res1' = some x := by
            cases r <;> simp only [resultToLoop] at h2r <;> exact ⟨_, h2r⟩
          subst hx
          have hx0 : x ≠ .continue 0 := by
            intro h; subst h; cases r <;> simp_all [resultToLoop]
          have hx1 : x ≠ .break 0 := by
            intro h; subst h; cases r <;> simp_all [resultToLoop]
          have hb : LoopSemStateFiniteExact.evaluate B
              { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + ck') } =
              (some x, t1) := by
            rw [hbodyK, seq_continue_some h2']; rfl
          refine ⟨ck + ck', _, _, by omega, loop_step_exit (L' := l) hx0 hx1 (hentryK _) hb, h2s, h2m, h2g,
            h2c, ?_, localsResultRel_exitLoop ctxt l _ _ r h2l⟩
          rw [h2r]
          exact resultToLoop_exitLoop r hr0 hr1

end InitECandidate.Solver.CrepToLoopBound
#print axioms InitECandidate.Solver.CrepToLoopBound.simulateWhile
