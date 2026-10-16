import InitECandidate.Solver.StackAllocBound.Common

/-! Expose the actual zero-clock witnesses for the nonrecursive cases of
Stack allocation lowering. All original guards and postconditions remain. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open Flapjack.StackSemShMem
open Classical

variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

theorem goal_skip (s : StackSemStateFiniteExact width C F) :
    ZeroGoal anything cr (.skip : HolProg width) s := by
  intro r t m n c regs h _ _ hpre
  rw [evaluate_skip] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨0, regs, rfl, evaluate_skip _, hpre.regs, hpre.buf, fun _ => hpre.stack⟩

theorem goal_break (s : StackSemStateFiniteExact width C F) (v : Nat) :
    ZeroGoal anything cr (.break v : HolProg width) s := by
  intro r t m n c regs h _ _ hpre
  rw [evaluate_break] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨0, regs, rfl, evaluate_break _ _, hpre.regs, hpre.buf, fun _ => hpre.stack⟩

theorem goal_continue (s : StackSemStateFiniteExact width C F) (v : Nat) :
    ZeroGoal anything cr (.continue v : HolProg width) s := by
  intro r t m n c regs h _ _ hpre
  rw [evaluate_continue] at h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  exact ⟨0, regs, rfl, evaluate_continue _ _, hpre.regs, hpre.buf, fun _ => hpre.stack⟩

theorem goal_halt (s : StackSemStateFiniteExact width C F) (v : Nat) :
    ZeroGoal anything cr (.halt v : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_halt] at h
  split at h
  · rename_i w hw
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun h => absurd rfl (h w)⟩
    show evaluate (.halt v, Res anything cr c s regs) = _
    rw [evaluate_halt, getVar_res anything cr c s regs hpre.regs hw]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_ret (s : StackSemStateFiniteExact width C F) (v : Nat) :
    ZeroGoal anything cr (.ret v : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_ret] at h
  split at h
  · rename_i l1 l2 hw
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.ret v, Res anything cr c s regs) = _
    rw [evaluate_ret, getVar_res anything cr c s regs hpre.regs hw]
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_raise (s : StackSemStateFiniteExact width C F) (v : Nat) :
    ZeroGoal anything cr (.raise v : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_raise] at h
  split at h
  · rename_i l1 l2 hw
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.raise v, Res anything cr c s regs) = _
    rw [evaluate_raise, getVar_res anything cr c s regs hpre.regs hw]
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_tick (s : StackSemStateFiniteExact width C F) :
    ZeroGoal anything cr (.tick : HolProg width) s := by
  intro r t m n c regs h _ _ hpre
  rw [evaluate_tick] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.tick, Tgt anything cr c s ck regs) = _ ∧ _
  by_cases h0 : s.clock = 0
  · simp only [h0, if_true, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf, fun _ => ?_⟩
    · rw [evaluate_tick, tgt_zero]
      simp only [h0, if_true]
      rfl
    · simp [StackBound, emptyEnv]
      exact Nat.two_pow_pos width
  · simp only [h0, if_false, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    rw [evaluate_tick, tgt_zero]
    simp only [h0, if_false]
    rfl

theorem goal_inst (s : StackSemStateFiniteExact width C F) (i : Compiler.Encoders.Asm.HolInst width) :
    ZeroGoal anything cr (.inst i : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_inst] at h
  split at h
  · rename_i s1 hs1
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb := hpre.buf
    obtain ⟨regs1, he, hsub, hst, hbuf⟩ := inst_correct (compile_rest := cr)
      (anything := anything) (c := c) ⟨hs1, hpre.stack, by unfold BufBound at hb; omega, hpre.regs⟩
    refine ⟨0, regs1, rfl, ?_, hsub, by unfold BufBound; omega, fun _ => hst⟩
    show evaluate (.inst i, Res anything cr c s regs) = _
    rw [evaluate_inst, he]
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_get (s : StackSemStateFiniteExact width C F) (v : Nat) (name : StoreName) :
    ZeroGoal anything cr (.get v name : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_get] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hS
  split at h
  · rename_i x hx
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.get v name, Res anything cr c s regs) = _
    rw [evaluate_get]
    simp only [hx]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_set (s : StackSemStateFiniteExact width C F) (name : StoreName) (v : Nat) :
    ZeroGoal anything cr (.set name v : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_set] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  split at h
  · rename_i x hx
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.set name v, Res anything cr c s regs) = _
    rw [evaluate_set]
    simp only [getVar_res anything cr c s regs hpre.regs hx]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem instRel_res (c : DataToWord.Config) (s : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (hsub : s.regs.submap regs) :
    InstCorrectSupport.InstRel s (Res anything cr c s regs) :=
  ⟨hsub, rfl, rfl, rfl, rfl, rfl⟩

theorem goal_opCurrHeap (s : StackSemStateFiniteExact width C F) (b : Compiler.Encoders.Asm.HolBinop) (v src : Nat) :
    ZeroGoal anything cr (.opCurrHeap b v src : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_opCurrHeap] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  split at h
  · rename_i x hx
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.opCurrHeap b v src, Res anything cr c s regs) = _
    rw [evaluate_opCurrHeap]
    simp only [InstCorrectSupport.wordExp_rel (instRel_res anything cr c s regs hpre.regs) _ _ hx]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

open Classical
theorem goal_locValue (s : StackSemStateFiniteExact width C F) (v l1 l2 : Nat) :
    ZeroGoal anything cr (.locValue v l1 l2 : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_locValue] at h
  split at h
  · rename_i hl
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    show evaluate (.locValue v l1 l2, Res anything cr c s regs) = _
    rw [evaluate_locValue, if_pos (loc_check_compile ⟨hl, fun k p hk => (hpre.code k p hk).1⟩)]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

omit [NeZero width] in
theorem two_pow_pos' : 0 < 2 ^ width := Nat.two_pow_pos width

theorem stackBound_emptyEnv (s : StackSemStateFiniteExact width C F) : StackBound (emptyEnv s) := by
  simp only [StackBound, emptyEnv, List.length_nil, Nat.zero_mul]
  exact two_pow_pos'

theorem goal_stackAlloc (s : StackSemStateFiniteExact width C F) (k : Nat) :
    ZeroGoal anything cr (.stackAlloc k : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackAlloc] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackAlloc k, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i hlt
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf,
      fun _ => stackBound_emptyEnv _⟩
    rw [tgt_zero, evaluate_stackAlloc]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hlt, if_true]
    rfl
  · rename_i hlt
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    rw [tgt_zero, evaluate_stackAlloc]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hlt]

theorem goal_stackFree (s : StackSemStateFiniteExact width C F) (k : Nat) :
    ZeroGoal anything cr (.stackFree k : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackFree] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackFree k, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · rename_i hlt
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    rw [tgt_zero, evaluate_stackFree]
    simp only [Bool.not_true, Bool.false_eq_true, if_false, hlt]

theorem goal_stackLoad (s : StackSemStateFiniteExact width C F) (a k : Nat) :
    ZeroGoal anything cr (.stackLoad a k : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackLoad] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackLoad a k, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i hlt
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
    rw [tgt_zero, evaluate_stackLoad]
    simp only [Bool.not_true, Bool.false_eq_true, if_false]
    rw [dif_pos hlt]
    rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_stackLoadAny (s : StackSemStateFiniteExact width C F) (a rn : Nat) :
    ZeroGoal anything cr (.stackLoadAny a rn : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackLoadAny] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackLoadAny a rn, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i w hw

    split at h
    · rename_i hlt
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
      rw [tgt_zero, evaluate_stackLoadAny]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        getVar_res anything cr c s regs hpre.regs hw]
      rw [dif_pos hlt]
      rfl
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_stackStore (s : StackSemStateFiniteExact width C F) (a k : Nat) :
    ZeroGoal anything cr (.stackStore a k : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackStore] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackStore a k, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hle
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  · rename_i v hv
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => ?_⟩
    · rw [tgt_zero, evaluate_stackStore]
      simp only [Bool.not_true, Bool.false_eq_true, if_false, hle,
        getVar_res anything cr c s regs hpre.regs hv]
    · have := hpre.stack
      simpa [StackBound] using this

theorem goal_stackStoreAny (s : StackSemStateFiniteExact width C F) (a rn : Nat) :
    ZeroGoal anything cr (.stackStoreAny a rn : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackStoreAny] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackStoreAny a rn, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i v w hv hw

    split at h
    · rename_i hlt
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => ?_⟩
      · rw [tgt_zero, evaluate_stackStoreAny]
        simp only [Bool.not_true, Bool.false_eq_true, if_false,
          getVar_res anything cr c s regs hpre.regs hv,
          getVar_res anything cr c s regs hpre.regs hw]
        rw [if_pos hlt]
      · have := hpre.stack
        simpa [StackBound] using this
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_stackGetSize (s : StackSemStateFiniteExact width C F) (a : Nat) :
    ZeroGoal anything cr (.stackGetSize a : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackGetSize] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
  show evaluate (.stackGetSize a, Res anything cr c s regs) = _
  rw [evaluate_stackGetSize]
  rfl

theorem goal_stackSetSize (s : StackSemStateFiniteExact width C F) (a : Nat) :
    ZeroGoal anything cr (.stackSetSize a : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_stackSetSize] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_eq_true, if_false] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.stackSetSize a, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i w hw
    split at h
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
    · rename_i hle
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
      rw [tgt_zero, evaluate_stackSetSize]
      simp only [Bool.not_true, Bool.false_eq_true, if_false,
        getVar_res anything cr c s regs hpre.regs hw, hle]
      rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_bitmapLoad (s : StackSemStateFiniteExact width C F) (a v : Nat) :
    ZeroGoal anything cr (.bitmapLoad a v : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_bitmapLoad] at h
  simp only [hpre.useStack, Bool.not_true, Bool.false_or] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.bitmapLoad a v, Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hav
  split at h
  · rename_i w hw
    split at h
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
    · rename_i hle
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, _, rfl, ?_, submap_fupdate_both hpre.regs, hpre.buf, fun _ => hpre.stack⟩
      rw [tgt_zero, evaluate_bitmapLoad]
      simp only [Bool.not_true, Bool.false_or, hav,
        getVar_res anything cr c s regs hpre.regs hw]
      rw [dif_neg hle]
      rfl
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem shMemOp_res (c : DataToWord.Config) (s s1 : StackSemStateFiniteExact width C F)
    (regs : HolFiniteMapExact Nat (WordLocW width)) (hsub : s.regs.submap regs)
    (op : Compiler.Encoders.Asm.HolMemop) (v : Nat) (a : BitVec width)
    (res : Option (StackSemResult width)) (hres : res ≠ some .error)
    (h : shMemOp op v a s = (res, s1)) :
    ∃ regs1, shMemOp op v a (Res anything cr c s regs) = (res, Res anything cr c s1 regs1) ∧
      s1.regs.submap regs1 ∧ BufBound s1 = BufBound s ∧ s1.stack = s.stack := by
  cases op <;> simp only [shMemOp, shMemLoad, shMemStore, shMemLoadByte, shMemStoreByte,
    shMemLoad16, shMemStore16, shMemLoad32, shMemStore32] at h ⊢
  all_goals repeat' split at h
  all_goals simp only [Prod.mk.injEq] at h
  all_goals obtain ⟨rfl, rfl⟩ := h
  all_goals try exact absurd rfl hres
  all_goals try rw [getVar_res anything cr c s regs hsub ‹getVar v s = some _›]
  all_goals first
    | exact ⟨regs, by simp only [*, if_true], hsub, rfl, rfl⟩
    | exact ⟨regs.updateEq _, by simp only [*, if_true], submap_fupdate_both hsub, rfl, rfl⟩

theorem goal_shMemOp (s : StackSemStateFiniteExact width C F)
    (op : Compiler.Encoders.Asm.HolMemop) (v : Nat) (addr : Compiler.Encoders.Asm.HolAddr width) :
    ZeroGoal anything cr (.shMemOp op v addr : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  obtain ⟨a, w⟩ := addr
  rw [evaluate_shMemOp] at h
  show ∃ ck regs1, ck = 0 ∧ evaluate (.shMemOp op v (.addr a w), Tgt anything cr c s ck regs) = _ ∧ _
  split at h
  · rename_i a' ha
    by_cases h0 : s.clock = 0
    · simp only [h0, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, HolFiniteMapExact.empty, rfl, ?_, submap_empty _, hpre.buf,
        fun _ => stackBound_emptyEnv _⟩
      rw [tgt_zero, evaluate_shMemOp,
        InstCorrectSupport.wordExp_rel (instRel_res anything cr c s regs hpre.regs) _ _ ha]
      simp only [h0, if_true]
      rfl
    · simp only [h0, if_false] at h
      obtain ⟨regs1, he, hsub, hbuf, hst⟩ :=
        shMemOp_res anything cr c (decClock s) t regs hpre.regs op v a' r hr h
      refine ⟨0, regs1, rfl, ?_, hsub, hbuf ▸ hpre.buf, fun _ => by
        unfold StackBound; rw [hst]; exact hpre.stack⟩
      rw [tgt_zero, evaluate_shMemOp,
        InstCorrectSupport.wordExp_rel (instRel_res anything cr c s regs hpre.regs) _ _ ha]
      simp only [h0, if_false]
      exact he
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_codeBufferWrite (s : StackSemStateFiniteExact width C F) (a b : Nat) :
    ZeroGoal anything cr (.codeBufferWrite a b : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_codeBufferWrite] at h
  split at h
  · rename_i w1 w2 h1 h2
    split at h
    · rename_i cb hcb
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
      show evaluate (.codeBufferWrite a b, Res anything cr c s regs) = _
      rw [evaluate_codeBufferWrite, getVar_res anything cr c s regs hpre.regs h1,
        getVar_res anything cr c s regs hpre.regs h2]
      simp only [hcb]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem goal_dataBufferWrite (s : StackSemStateFiniteExact width C F) (a b : Nat) :
    ZeroGoal anything cr (.dataBufferWrite a b : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_dataBufferWrite] at h
  simp only [hpre.useStack, not_true_eq_false, if_false] at h
  split at h
  · rename_i w1 w2 h1 h2
    split at h
    · rename_i db hdb
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨0, regs, rfl, ?_, hpre.regs, ?_, fun _ => hpre.stack⟩
      · show evaluate (.dataBufferWrite a b, Res anything cr c s regs) = _
        rw [evaluate_dataBufferWrite, getVar_res anything cr c s regs hpre.regs h1,
          getVar_res anything cr c s regs hpre.regs h2]
        simp only [not_true_eq_false, if_false, hdb]
      · have hb := hpre.buf
        simp only [wordSemBufferWrite] at hdb
        split at hdb
        · rename_i hc
          simp only [Option.some.injEq] at hdb
          subst hdb
          unfold BufBound at hb ⊢
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        · simp at hdb
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

theorem restrictIn_submap {m1 m2 : HolFiniteMapExact Nat (WordLocW width)} (keep : Nat → Bool)
    (h : m1.submap m2) : (restrictIn m1 keep).submap (restrictIn m2 keep) := by
  intro k v hk
  simp only [restrictIn] at hk ⊢
  split at hk
  · rw [if_pos ‹_›]; exact h _ _ hk
  · simp at hk

theorem goal_ffi (s : StackSemStateFiniteExact width C F) (fi : Basis.Pure.MlString.MlString)
    (p1 p2 p3 p4 p5 : Nat) :
    ZeroGoal anything cr (.ffi fi p1 p2 p3 p4 p5 : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_ffi] at h
  split at h
  · rename_i w1 w2 w3 w4 h1 h2 h3 h4
    show ∃ ck regs1, ck = 0 ∧ evaluate (.ffi fi p1 p2 p3 p4 p5, Tgt anything cr c s ck regs) = _ ∧ _
    split at h
    · rename_i b1 b2 hb1 hb2
      split at h
      · rename_i outcome hcall
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, regs, rfl, ?_, hpre.regs, hpre.buf, fun _ => hpre.stack⟩
        rw [tgt_zero, evaluate_ffi, getVar_res anything cr c s regs hpre.regs h1,
          getVar_res anything cr c s regs hpre.regs h2, getVar_res anything cr c s regs hpre.regs h3,
          getVar_res anything cr c s regs hpre.regs h4]
        simp only [hb1, hb2, hcall]
      · rename_i newFfi newBytes hcall
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨0, _, rfl, ?_, restrictIn_submap _ hpre.regs, hpre.buf, fun _ => hpre.stack⟩
        rw [tgt_zero, evaluate_ffi, getVar_res anything cr c s regs hpre.regs h1,
          getVar_res anything cr c s regs hpre.regs h2, getVar_res anything cr c s regs hpre.regs h3,
          getVar_res anything cr c s regs hpre.regs h4]
        simp only [hb1, hb2, hcall]
    · simp only [Prod.mk.injEq] at h
      exact absurd h.1.symm hr
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.goal_skip
#print axioms InitECandidate.Solver.StackAllocBound.goal_break
#print axioms InitECandidate.Solver.StackAllocBound.goal_continue
#print axioms InitECandidate.Solver.StackAllocBound.goal_halt
#print axioms InitECandidate.Solver.StackAllocBound.goal_ret
#print axioms InitECandidate.Solver.StackAllocBound.goal_raise
#print axioms InitECandidate.Solver.StackAllocBound.goal_tick
#print axioms InitECandidate.Solver.StackAllocBound.goal_inst
#print axioms InitECandidate.Solver.StackAllocBound.goal_get
#print axioms InitECandidate.Solver.StackAllocBound.goal_set
#print axioms InitECandidate.Solver.StackAllocBound.goal_opCurrHeap
#print axioms InitECandidate.Solver.StackAllocBound.goal_locValue
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackAlloc
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackFree
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackLoad
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackLoadAny
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackStore
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackStoreAny
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackGetSize
#print axioms InitECandidate.Solver.StackAllocBound.goal_stackSetSize
#print axioms InitECandidate.Solver.StackAllocBound.goal_bitmapLoad
#print axioms InitECandidate.Solver.StackAllocBound.goal_shMemOp
#print axioms InitECandidate.Solver.StackAllocBound.goal_codeBufferWrite
#print axioms InitECandidate.Solver.StackAllocBound.goal_dataBufferWrite
#print axioms InitECandidate.Solver.StackAllocBound.goal_ffi
