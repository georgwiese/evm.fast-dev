import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Alloc

namespace InitECandidate.Solver.WordToStackBound.Alloc
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Alloc

theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (dest : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.alloc dest names) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, hbsn, hbsl, hpre, -,
    maxVar⟩ := premises
  obtain ⟨rfl, hc1, hc2⟩ := allocConventions k dest names conventions
  have hn1 : ∀ x, sptDomain names.1 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc1 x hx).1, by have := (hc1 x hx).2; omega⟩
  have hn2 : ∀ x, sptDomain names.2 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc2 x hx).1, by have := (hc2 x hx).2; omega⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, -, -, -, r7, -, -, r10, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, r35, -, -, -, -⟩ := related'
  -- the allocation request comes from source variable 2, i.e. target register 1
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hg : WordSemStateFiniteExact.getVar 2 source with _ | (w | ⟨_, _⟩)
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  rotate_left
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only [hg] at execution
  have hg1 : StackSemStateOps.getVar 1 target = some (.word w) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 2 _
      ⟨related, hg, rfl, by omega⟩
  rcases hcut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [WordSemStateFiniteExact.alloc, hcut, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [compNative] at compilation
  rcases hwl : wLiveNative names (bs, n) (k, f, frame) with ⟨q1, bsw⟩
  rw [hwl] at compilation
  simp only [Prod.mk.injEq] at compilation
  obtain ⟨rfl, rfl⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  -- the result relation for a simulated allocation
  have finish : ∀ (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
      (result = none → res1 = none ∧ stateRel ac k f frame sourcePost t1 lens 0) →
      (result ≠ none → result = some .notEnoughSpace ∧ res1 = some (.halt (.word 1)) ∧
          sourcePost.clock = t1.clock ∧ sourcePost.ffi = t1.ffi) →
      compCorrectResult ac k f frame source sourcePost t1 result res1 lens := by
    intro t1 res1 hnone hsome
    unfold compCorrectResult
    by_cases hres : result = none
    · obtain ⟨rfl, hrel1⟩ := hnone hres
      subst hres
      simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
      exact hrel1
    · obtain ⟨rfl, rfl, hcl, hff⟩ := hsome hres
      simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
      exact ⟨hff, hcl⟩
  by_cases hf : 1 ≤ f
  · obtain ⟨t5, hev5, hpush5, hrel5, -, -, hget5⟩ :=
      EvaluateWLive.evaluateWLive ac k f frame names bs n q1 bsPost nPost source target lens envs
        ⟨by rw [hwl], hn1, hn2, related, hf, hcut, hbsn, hbsl, hpre⟩
    have hrel5' := hrel5
    unfold stateRel at hrel5'
    have hclock5 : t5.clock = target.clock := hrel5'.1.symm.trans r1
    have huse5 : t5.useAlloc = true := hrel5'.2.2.2.2.2.2.1
    have hg5 : StackSemStateOps.getVar 1 t5 = some (.word w) :=
      (hget5 1 (by omega)).trans hg1
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc ac k f frame w names source sourcePost result t5 lens envs
        ⟨execution, hn1, hn2, hf, hrel5, hpush5, hcut, notError⟩
    refine ⟨0, t1, res1, Nat.zero_le _, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, hev5]
    simp only [StackSemControl.fixClock]
    rw [show min target.clock t5.clock = t5.clock by omega]
    show StackSemEvaluate.evaluate (Prog.alloc 1, t5) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [huse5, Bool.not_true, Bool.false_eq_true, if_false, hg5]
    exact halloc1
  · have hf0 : f = 0 := by omega
    have hfr0 : frame = 0 := by
      by_cases h : frame = 0
      · exact h
      · rw [if_neg h] at r35; omega
    subst hf0 hfr0
    simp only [wLiveNative, if_true, Prod.mk.injEq] at hwl
    obtain ⟨rfl, -⟩ := hwl
    -- with no frame, the stack-placed cutset names cannot exist
    have hempty : ∀ t : Spt Unit, (∀ x, sptDomain t x → 2 * k ≤ x) →
        maxList ((sptToAList t).map Prod.fst) < 2 * k → sptDomain t = fun _ => False := by
      intro t hge hlt
      funext x
      apply propext
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
        have hm := maxList_ge_of_mem ((sptToAList t).map Prod.fst) x
          (List.mem_map.mpr ⟨(x, u), (sptToAList_mem_iff_lookup t x u).mpr hu, rfl⟩)
        have := hge x hx
        omega
      · exact False.elim
    simp only [maxVarHOL, cutsetsMaxHOL, max_lt_iff] at maxVar
    have hd1 := hempty names.1 (fun x hx => (hc1 x hx).2) (by omega)
    have hd2 := hempty names.2 (fun x hx => (hc2 x hx).2) (by omega)
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc2 ac k w names source sourcePost result target lens
        ⟨execution, related, hd1, hd2, notError⟩
    refine ⟨0, t1, res1, Nat.zero_le _, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
    simp only [StackSemControl.fixClock, Nat.min_self]
    show StackSemEvaluate.evaluate (Prog.alloc 1, target) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [r7, Bool.not_true, Bool.false_eq_true, if_false, hg1]
    exact halloc1

end InitECandidate.Solver.WordToStackBound.Alloc
#print axioms InitECandidate.Solver.WordToStackBound.Alloc.compCorrectAlloc
