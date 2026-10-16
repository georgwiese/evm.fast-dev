import InitECandidate.Solver.FlattenWeighted.Sequence
import InitECandidate.Solver.FlattenBound.Arithmetic
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.If

/-! Result transport and prefix composition retain explicit execution credits. -/
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

/-- Composition for a branch that produces a result: the final program
counter is irrelevant. -/
theorem paidConclComposeSome (wholeCredit subCredit : Nat) {p p' : HolProg width} {t t' : Bool}
    {x : StackSemResult width} {s1 middle s2 : StackSemStateFiniteExact width C F}
    {n l l' : Nat} {cs bs : List Nat} {ck : Nat}
    {t1 t2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (run : ∀ ck1, evaluate { t1 with clock := t1.clock + ck + ck1 } =
      evaluate { t2 with clock := t2.clock + ck1 })
    (e1 : t2.lenReg = t1.lenReg) (e2 : t2.ptrReg = t1.ptrReg) (e3 : t2.len2Reg = t1.len2Reg)
    (e4 : t2.ptr2Reg = t1.ptr2Reg) (e5 : t2.linkReg = t1.linkReg) (pre : t1.code <+: t2.code)
    (small : ck + 4 * subCredit ≤ 4 * wholeCredit)
    (h : PaidConcl subCredit p' middle t' (some x) s2 n l' cs bs t2) :
    PaidConcl wholeCredit p s1 t (some x) s2 n l cs bs t1 := by
  obtain ⟨ck', t3, bounded, h⟩ := h
  refine ⟨ck + ck', t3, by omega, ?_⟩
  revert h
  cases haltView (some x) with
  | some res =>
    rintro ⟨ev, ffi⟩
    exact ⟨by rw [← Nat.add_assoc, run ck', ev], ffi⟩
  | none =>
    rintro ⟨run2, f1, f2, f3, f4, f5, pre2, rest⟩
    refine ⟨fun ck1 => ?_, by rw [f1, e1], by rw [f2, e2], by rw [f3, e3], by rw [f4, e4],
      by rw [f5, e5], pre.trans pre2, ?_⟩
    · rw [show t1.clock + (ck + ck') + ck1 = t1.clock + ck + (ck' + ck1) by omega, run,
        ← run2 ck1, Nat.add_assoc]
    · revert rest
      simp only [Option.map_some]
      cases resultView x n cs bs <;> exact id

/-- Results with the same halt view and result view have the same
conclusion, for any program, label stacks and next label. -/
theorem paidConclResult (firstCredit secondCredit : Nat) {p p' : HolProg width} {t t' : Bool} {x y : StackSemResult width}
    {s1 s2 : StackSemStateFiniteExact width C F} {n n' l l' : Nat} {cs bs cs' bs' : List Nat}
    {t1 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (size : firstCredit ≤ secondCredit)
    (hh : haltView (some x) = haltView (some y))
    (hr : resultView x n cs bs = resultView y n' cs' bs')
    (h : PaidConcl firstCredit p s1 t (some x) s2 n l cs bs t1) :
    PaidConcl secondCredit p' s1 t' (some y) s2 n' l' cs' bs' t1 := by
  obtain ⟨ck, t2, small, h⟩ := h
  refine ⟨ck, t2, ?_, ?_⟩
  · omega
  revert h
  rw [hh]
  cases haltView (some y) with
  | some res => exact id
  | none =>
    simp only [Option.map_some, hr]
    cases resultView y n' cs' bs' <;> exact id

end
end InitECandidate.Solver.FlattenWeighted
#print axioms InitECandidate.Solver.FlattenWeighted.paidConclComposeSome
#print axioms InitECandidate.Solver.FlattenWeighted.paidConclResult
