import InitECandidate.Solver.FlattenBound.Assembly
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect

/-! Whole-entry execution retains the flattening clock bound and the original
return-to-halting-procedure premise, including timeouts and final FFI results. -/
namespace InitECandidate.Solver.FlattenBound
open Flapjack.Compiler.Backend
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCallCorrect

def callBudget (limit clock : Nat) : Nat := 4 * ((limit + 1) * clock + 2 * limit)

theorem boundedCallCorrect {width : Nat} [NeZero width] {C F : Type} {start : Nat}
    {s1 s2 : StackSemStateFiniteExact width C F} {res : Option (StackSemResult width)}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (limit : Nat) (safe : StateOk limit s1) :
    StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width), s1) = (res, s2) ∧
    stateRel s1 t1 ∧
    locToPc start 0 t1.code = some t1.pc ∧
    res ≠ some .error ∧
    (res ≠ some .timeOut →
      (∃ w : BitVec width, res = some (.halt (.word w))) ∨
      (∃ f, res = some (.finalFFI f)) ∨
      (∃ n, res = some (.result (.loc n 0)) ∧
        ∀ s : StackSemStateFiniteExact width C F, sptSubspt s1.code s.code ∧ s.clock ≠ 0 →
          ∃ t, StackSemEvaluate.evaluate ((.call none (.inl n) none : HolProg width), s) =
              (some (.halt (.word 0)), t) ∧
            t.ffi = s.ffi ∧ t.clock = s.clock - 1)) →
    ∃ (ck : Nat) (r2 : MachineResult) (t2 : Flapjack.Compiler.Backend.LabSem.State width C F),
      ck ≤ callBudget limit s1.clock ∧
      evaluate { t1 with clock := t1.clock - 1 + ck } = (r2, t2) ∧
      (∀ f, res = some (.finalFFI f) → r2 = .halt (.ffiOutcome f)) ∧
      (∀ w, res = some (.halt w) → r2 =
        match w with
        | .word w => if w = 0 then .halt .success else .halt .resourceLimitHit
        | _ => .error) ∧
      (∀ n, res = some (.result (.loc n 0)) → r2 = .halt .success) ∧
      t2.ffi = s2.ffi ∧
      r2 ≠ .error ∧ (res = some .timeOut → r2 = .timeOut) := by
  rintro ⟨ev, rel, hpc, nerr, hres⟩
  have clk := relClock rel
  obtain ⟨prog, hlook, ⟨h0, rfl, rfl⟩ | ⟨h0, x, rfl, hbad, e2⟩⟩ := callNoneInlCases ev nerr
  · -- clock zero: both sides time out at once
    refine ⟨0, .timeOut, { t1 with clock := t1.clock - 1 + 0 }, Nat.zero_le _, ?_, by simp, by simp, by simp,
      ?_, by simp, fun _ => rfl⟩
    · rw [evaluate, if_pos (by simp; omega)]
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
  obtain ⟨caP, pc', instP, entry⟩ := relCode rel hlook
  rw [hpc] at entry
  cases entry
  have rel' : stateRel (StackSemStateOps.decClock s1) { t1 with clock := t1.clock - 1 } :=
    StateRel.stateRelDecClock rel
  have nx : x ≠ .error := fun h => nerr (by rw [h])
  have progOk := safe.1 start prog hlook
  obtain ⟨ck, t2, small, h⟩ := boundedPropAll limit prog (StackSemStateOps.decClock s1)
    progOk safe true (some x) s2
    start (StackAlloc.nextLabHOL prog 2) [] [] { t1 with clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [hpc]⟩
  have single : ck ≤ callBudget limit s1.clock := by
    apply Nat.le_trans small
    have progSize := progOk.1
    unfold budget callBudget
    have spent : (StackSemStateOps.decClock s1).clock - s2.clock ≤ s1.clock := by
      simp only [StackSemStateOps.decClock]; omega
    have scaled := Nat.mul_le_mul_left (limit + 1) spent
    change 4 * ((limit + 1) * ((StackSemStateOps.decClock s1).clock - s2.clock) + nodes prog) ≤ _
    omega
  rcases x with v | v | k | k | v | _ | f | _
  · -- `Result v`: only `Loc n 0` is allowed, and procedure `n` halts
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, hh⟩ := hres (by simp)
    · simp at hw
    · simp at hf
    simp only [Option.some.injEq, StackSemResult.result.injEq] at hn
    subst hn
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hcover, hw⟩ := h
    have hsub : sptSubspt s1.code s2.code := by
      simpa [StackSemStateOps.decClock] using (StackProps.EvaluateMono.evaluateMono _ _ _ _ e2).2
    obtain ⟨t, evh, tffi, tclock⟩ := hh { s2 with clock := s2.clock + 1 } ⟨hsub, by simp⟩
    obtain ⟨prog2, hlook2, ⟨h0', -⟩ | ⟨-, x2, hx2, -, e3⟩⟩ := callNoneInlCases evh (by simp)
    · simp at h0'
    simp only [Option.some.injEq] at hx2
    subst hx2
    have hdc : StackSemStateOps.decClock { s2 with clock := s2.clock + 1 } = s2 := by
      simp [StackSemStateOps.decClock]
    rw [hdc] at e3
    simp only at hlook2
    obtain ⟨w, hw'⟩ := Option.isSome_iff_exists.mp (hcover n (by simp [hlook2]))
    obtain ⟨rfl, rel2⟩ := hw w hw'
    obtain ⟨caP2, pc2, instP2, entry2⟩ := relCode rel2 hlook2
    rw [hw'] at entry2
    cases entry2
    have postOk : StateOk limit s2 := stateOk_evaluate limit prog (StackSemStateOps.decClock s1) s2 _ safe e2
    have prog2Ok := postOk.1 n prog2 hlook2
    obtain ⟨ck', t3, small2, h3⟩ := boundedPropAll limit prog2 s2 prog2Ok postOk true (some (.halt (.word 0))) t n
      (StackAlloc.nextLabHOL prog2 2) [] [] t2 ⟨e3, by simp, rel2, caP2, instP2, by simp [hw']⟩
    simp only [haltView, haltWordView, if_true] at h3
    have combined : ck + ck' ≤ callBudget limit s1.clock := by
      have firstSize := progOk.1
      have secondSize := prog2Ok.1
      have sameClock : t.clock = s2.clock := by simpa using tclock
      have spent : (StackSemStateOps.decClock s1).clock - s2.clock ≤ s1.clock := by
        simp only [StackSemStateOps.decClock]; omega
      have scaled := Nat.mul_le_mul_left (limit + 1) spent
      simp only [budget, sameClock, Nat.sub_self, Nat.mul_zero, Nat.zero_add] at small small2
      unfold callBudget
      omega
    refine ⟨ck + ck', .halt .success, t3, combined, ?_, by simp, by simp, fun _ _ => rfl, ?_, by simp,
      by simp⟩
    · have r1 := run ck'
      rw [show t1.clock - 1 + (ck + ck') = t1.clock - 1 + ck + ck' by omega, r1]
      exact h3.1
    · rw [h3.2, tffi]
  · -- `Exception`: excluded by the hypothesis
    rcases hres (by simp) with ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩
    · simp at hw
    · simp at hf
    · simp at hn
  · simp [StackSemControl.badFunReturn] at hbad
  · simp [StackSemControl.badFunReturn] at hbad
  · -- `Halt v`
    obtain ⟨w, hw⟩ | ⟨f, hf⟩ | ⟨n, hn, -⟩ := hres (by simp)
    · simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw
      subst hw
      simp only [haltView] at h
      refine ⟨ck, haltWordView (.word w), t2, single, h.1, by simp, ?_, by simp, h.2, ?_, by simp⟩
      · intro w' hw'
        simp only [Option.some.injEq, StackSemResult.halt.injEq] at hw'
        subst hw'
        rfl
      · simp only [haltWordView]; split <;> simp
    · simp at hf
    · simp at hn
  · -- `TimeOut`
    simp only [haltView, Option.map_some, resultView] at h
    obtain ⟨run, -, -, -, -, -, -, hffi, hclk⟩ := h
    refine ⟨ck, .timeOut, { t2 with clock := t2.clock + 0 }, single, ?_, by simp, by simp, by simp,
      hffi, by simp, fun _ => rfl⟩
    have r0 := run 0
    simp only [Nat.add_zero] at r0 ⊢
    rw [r0, evaluate, if_pos (by simp [hclk])]
  · -- `FinalFFI f`
    simp only [haltView] at h
    refine ⟨ck, _, t2, single, h.1, ?_, by simp, by simp, h.2, by simp, by simp⟩
    intro f' hf'
    simp only [Option.some.injEq, StackSemResult.finalFFI.injEq] at hf'
    rw [hf']
  · exact (nx rfl).elim

end InitECandidate.Solver.FlattenBound
#print axioms InitECandidate.Solver.FlattenBound.boundedCallCorrect
