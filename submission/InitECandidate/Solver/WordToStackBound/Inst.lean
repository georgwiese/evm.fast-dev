import InitECandidate.Solver.WordToStackBound.Common
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Inst

namespace InitECandidate.Solver.WordToStackBound.Inst
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.Inst

private theorem instArgConvention_ofWordLangInst {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    instArgConvention i = instArgConventionExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | ⟨_, _⟩ | ⟨a⟩ | ⟨_, _, _⟩
  all_goals try rfl
  rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  all_goals (cases ri <;> rfl)

theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (i : WordLangInst (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    Simulation ac limit (.inst i) source := by
  intro safe supported bounded k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, _flat,
    compilation, _lengthBound, _bitmapBound, _bitmapPrefix, _labels, maxBound⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases instRun : WordSemStateFiniteExact.inst i source with _ | post
  · rw [instRun] at execution
    obtain ⟨rfl, -⟩ := Prod.mk.inj execution
    exact absurd rfl notError
  · rw [instRun] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    have conventionParts := conventions
    simp only [postAllocConventionsHOL, everyVarHOL, callArgConventionHOL,
      Bool.and_eq_true] at conventionParts
    obtain ⟨physical, _, convention⟩ := conventionParts
    simp only [compNative, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -⟩ := compilation
    obtain ⟨post', run, postRel, _, _⟩ :=
      InstSimulation.evaluateWInst ac (HolInst.ofWordLangInst i) k f frame source post
        target lens (by simpa only [HolInst.to_of] using instRun)
        (by simpa only [HolInst.to_of] using physical)
        (by simpa only [HolInst.to_of, maxVarHOL] using maxBound)
        (by rw [← instArgConvention_ofWordLangInst]; exact convention) related
    refine ⟨0, post', none, Nat.zero_le _, by simpa using run, ?_⟩
    simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, if_false]
    exact postRel

end InitECandidate.Solver.WordToStackBound.Inst
#print axioms InitECandidate.Solver.WordToStackBound.Inst.compCorrectInst
