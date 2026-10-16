import InitECandidate.Solver.FlattenBound.Jumps
import InitECandidate.Solver.FlattenWeighted.Results
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Call

/-! Bounded tail-call entry with the original indirect/direct call checks. -/
namespace InitECandidate.Solver.FlattenWeighted
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

/-- `Call` case without a return handler (a tail call). -/
theorem paidCallTail (credits : Nat) (s1 : StackSemStateFiniteExact width C F) (dest : Nat ⊕ Nat)
    (handler : Option (HolProg width × Nat × Nat))
    (callee : s1.clock ≠ 0 → ∀ prog,
      StackSemControl.findCode dest s1.regs s1.code = some prog →
      PaidProp credits prog (StackSemStateOps.decClock s1)) :
    PaidProp credits (.call none dest handler) s1 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -, inst, -⟩
  rw [StackSemEvaluate.evaluate_call] at ev
  simp only at ev
  have fetch : asmFetchAux t1.pc t1.code = some (Flapjack.Compiler.Backend.StackToLab.compileJumpHOL dest) :=
    fetchSingle (Prelude.notIsLabelCompileJump dest)
      (by simpa [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList] using inst)
  have err : ∀ {x : StackSemStateFiniteExact width C F},
      (some StackSemResult.error, x) = (r, s2) → False := fun e => by
    simp only [Prod.mk.injEq] at e; exact nerr e.1.symm
  have clk := relClock rel
  rcases hfind : StackSemControl.findCode dest s1.regs s1.code with _ | prog
  · rw [hfind] at ev; exact (err ev).elim
  rw [hfind] at ev
  simp only at ev
  rcases handler with _ | hd
  swap; · exact (err ev).elim
  simp only at ev
  obtain ⟨d, pc', hlook, entry, caP, instP, step⟩ :=
    compileJumpEnter (fun r v h => InstCorrect.regOfLookup rel h) rel fetch hfind
  by_cases h0 : s1.clock = 0
  · rw [if_pos h0] at ev
    simp only [Prod.mk.injEq] at ev
    obtain ⟨rfl, rfl⟩ := ev
    refine ⟨0, t1, Nat.zero_le _, fun _ => by simp, rfl, rfl, rfl, rfl, rfl, List.prefix_refl _, ?_, ?_⟩
    · simp [StackSemStateOps.emptyEnv, relFfi rel]
    · omega
  rw [if_neg h0, StackSemEvaluateClock.fixClockEvaluate] at ev
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
  have lt : MeasureLt prog (StackSemStateOps.decClock s1) (.call none dest none) s1 :=
    .inl (by simp [StackSemStateOps.decClock]; omega)
  have ph := callee h0 prog hfind true (some x') s' d (StackAlloc.nextLabHOL prog 2) [] []
    { t1 with pc := pc', clock := t1.clock - 1 }
    ⟨e2, nerr, rel', caP, instP, by simp [entry]⟩
  exact paidConclComposeSome credits credits (runEnter (by omega) step) rfl rfl rfl rfl rfl
    (List.prefix_refl _) (by omega)
    (paidConclResult credits credits (p' := prog) (t' := true) (l' := 0) (h := ph)
      (Nat.le_refl _) rfl (resultViewIndep hbad _ _ _ _ _ _))

end
end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.paidCallTail
