import InitECandidate.Solver.WordToStackBound.Assembly
import Mathlib.Tactic.NormNum

namespace InitECandidate.Solver.WordToStackBound.Entry
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect

private theorem evaluateSeqSkip {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (s : StackSemStateFiniteExact width C F) :
    StackSemEvaluate.evaluate (.seq .skip p, s) = StackSemEvaluate.evaluate (p, s) := by
  rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
  simp [StackSemControl.fixClock]

/-- Entry-call execution with a numerical clock bound, retaining both the
matching result/FFI branch and the original stack-overflow alternative. -/
theorem compCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) :
    ∀ (start : Nat) (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
      (t : StackSemStateFiniteExact width C F) (lens : List Nat),
      CodeSafe limit s.code →
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k 0 0 s t lens 0 →
      ∃ (ck : Nat) (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
        ck ≤ (2 * limit) * (s.clock - s1.clock) ∧
        t.clock + ck ≤ (2 * limit + 1) * s.clock ∧
        StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
          (res1, t1) ∧ (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
        (open Classical in if res.map compileResult = res1 then s1.ffi = t1.ffi ∧ s1.clock = t1.clock
         else res1 = some (.halt (.word 2)) ∧ List.IsPrefix t1.ffi.ioEvents s1.ffi.ioEvents ∧
           s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit) := by
  intro start s k res s1 t lens safe ⟨run, notError, related⟩
  have kBound : 4 < k := related.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ck, t1, res1, budget, targetRun, resultRel⟩ :=
    InitECandidate.Solver.WordToStackBound.compCorrect ac limit (.call none (some start) [0] none) s safe
      (by simp [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp])
      (by simp [ceiling, cost]) k 0 0 s1 t res
      .nil .nil t.bitmaps.length t.bitmaps.length (.seq .skip (.call none (.inl start) none)) lens
      ⟨run, notError, related, by simp [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, isPhyVar], by simp [flatExpConventions], by
        simp [compNative, callDestNative, seqStackFreeNative, Compiler.Backend.WordToStack.stackFree],
        by simp [appListAppend, appendAux], by simp [appListAppend, appendAux], by simp [appListAppend, appendAux],
        by simp [StackSem.getLabelsExact], by simp [maxVarHOL, maxList]; omega⟩
  have bound : ck ≤ (2 * limit) * (s.clock - s1.clock) := by
    simpa only [cost, Nat.add_zero] using budget
  have total : t.clock + ck ≤ (2 * limit + 1) * s.clock := by
    have clocks : s.clock = t.clock := related.1
    have spent := Nat.mul_le_mul_left (2 * limit) (Nat.sub_le s.clock s1.clock)
    rw [Nat.add_mul, Nat.one_mul]
    omega
  have wide : 8 ≤ width := by
    unfold stateRel at related
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩ := related
    exact h
  have oneLt : 1 < 2 ^ width := Nat.one_lt_two_pow (by omega)
  have twoLt : 2 < 2 ^ width :=
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) wide
  refine ⟨ck, t1, res1, bound, total, (evaluateSeqSkip _ _).symm.trans targetRun, ?_, ?_, ?_⟩
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt oneLt] at this
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt twoLt] at this
  · unfold compCorrectResult at resultRel
    by_cases same : res.map compileResult = res1
    · rw [if_pos same]
      rw [if_neg (not_not.mpr same)] at resultRel
      have ffiClock : ∀ {f frame lens' extra} {s' : WordSemStateFiniteExact width (Nat × C) F},
          stateRel ac k f frame s' t1 lens' extra → s'.ffi = t1.ffi ∧ s'.clock = t1.clock :=
        fun rel => ⟨rel.2.2.2.1.symm, rel.1⟩
      rcases res with _ | r
      · exact ffiClock resultRel
      · cases r with
        | result _ values => exact ffiClock resultRel.1
        | exception _ value =>
          obtain ⟨nonGc, gc, rel, _, _⟩ := resultRel
          exact ffiClock (s' := pushLocals nonGc gc s1) rel
        | «break» _ => exact ffiClock resultRel
        | «continue» _ => exact ffiClock resultRel
        | _ => exact resultRel
    · rw [if_neg same]
      rw [if_pos same] at resultRel
      exact resultRel


/-- When the source run stays within its stack limit, the bounded target run
has exactly the compiled result and complete FFI state. -/
theorem entrySimulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit start k : Nat)
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (result : Option (WordSemResult width))
    (safe : CodeSafe limit source.code)
    (related : stateRel ac k 0 0 source target lens 0)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) source = (result, post))
    (notError : result ≠ some .error)
    (space : post.stackMax.getD (post.stackLimit + 1) ≤ post.stackLimit) :
    ∃ extra targetPost,
      extra ≤ (2 * limit) * (source.clock - post.clock) ∧
      target.clock + extra ≤ (2 * limit + 1) * source.clock ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {target with clock := target.clock + extra}) = (result.map compileResult, targetPost) ∧
      targetPost.ffi = post.ffi ∧ targetPost.clock = post.clock := by
  classical
  obtain ⟨extra, targetPost, targetResult, budget, total, targetRun, _, _, outcome⟩ :=
    compCall ac limit start source k result post target lens safe ⟨run, notError, related⟩
  by_cases same : result.map compileResult = targetResult
  · rw [if_pos same] at outcome
    exact ⟨extra, targetPost, budget, total, by simpa only [same] using targetRun, outcome.1.symm, outcome.2.symm⟩
  · rw [if_neg same] at outcome
    omega

end InitECandidate.Solver.WordToStackBound.Entry
#print axioms InitECandidate.Solver.WordToStackBound.Entry.compCall
#print axioms InitECandidate.Solver.WordToStackBound.Entry.entrySimulation
