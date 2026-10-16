import InitECandidate.Solver.StackAllocBound.Common
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.AllocStore

/-! The un-stubbed StoreConsts used in runtime procedure 6 keeps its actual
zero-clock witness in allocation lowering. Copy-loop cost belongs to StackRemove. -/
namespace InitECandidate.Solver.StackAllocBound
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackAlloc
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect
open Flapjack Flapjack.StackSemStateOps Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.Compiler.Backend.StackProps
open Flapjack.Compiler.Backend.DataToWord Flapjack.Compiler.Backend.WordGcFunctions
open StackSemStoreConsts
open StackSemStoreConstsGuard
variable {width : Nat} [NeZero width] {C F : Type}
variable (anything : WordSemGcFun width) (cr : CompileFn width C)

theorem goal_storeConsts_none (s : StackSemStateFiniteExact width C F) (t1 t2 : Nat)
    : ZeroGoal anything cr (.storeConsts t1 t2 none : HolProg width) s := by
  intro r t m n c regs h hr _ hpre
  rw [evaluate_storeConsts] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hS
  rw [if_neg (by simp [hpre.useAlloc])] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hr
  rename_i hchk
  have hR : (s.regs.eraseEq 0).submap regs := by
    intro k v hk
    simp only [HolFiniteMapExact.lookup_eraseEq, FDOMSUB_HOL] at hk
    split at hk
    · simp at hk
    · exact hpre.regs _ _ hk
  obtain ⟨R1, he, hsub, -, -, -, hst, hbuf⟩ :=
    storeConstSem_res anything cr c s t regs hR hpre.useAlloc t1 t2 r hr h
  refine ⟨0, R1, rfl, ?_, hsub, hbuf ▸ hpre.buf, fun _ => by unfold StackBound; rw [hst]; exact hpre.stack⟩
  show evaluate (.storeConsts t1 t2 none, Res anything cr c s regs) = _
  rw [evaluate_storeConsts]
  simp only [not_true_eq_false, if_false, Option.isSome_none, Bool.false_eq_true, and_false]
  simp only [checkStoreConstsOpt, not_true_eq_false, if_false]
  exact he
end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.goal_storeConsts_none
