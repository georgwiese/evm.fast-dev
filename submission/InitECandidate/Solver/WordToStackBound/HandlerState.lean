import InitECandidate.Solver.WordToStackBound.CallState
import InitECandidate.Solver.WordToStackBound.Common

namespace InitECandidate.Solver.WordToStackBound
open Flapjack Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs.CompCorrect

theorem forgetSimulation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (limit : Nat) (program : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (simulation : Simulation ac limit program source)
    (safe : CodeSafe limit source.code)
    (supported : noInstallSubprogsHOL program = true)
    (bounded : ceiling program ≤ limit) : Seq.Simulation ac program source := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨extra,post,res,_,run,relation⟩ := simulation safe supported bounded
    k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  exact ⟨extra,post,res,run,relation⟩

theorem callHandlerSafe {width : Nat} [NeZero width] (limit : Nat)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (register : Nat) (body : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (supported : noInstallSubprogsHOL (.call ret dest args (some (register,body,l1,l2))) = true)
    (bounded : ceiling (.call ret dest args (some (register,body,l1,l2))) ≤ limit) :
    noInstallSubprogsHOL body = true ∧ ceiling body ≤ limit := by
  constructor
  · cases ret with
    | none => simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using supported
    | some descriptor =>
      rcases descriptor with ⟨values,names,code,r1,r2⟩
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.true_and, Bool.and_eq_true] at supported
      exact supported.2
  · cases ret with
    | none =>
      change max 0 (max 0 (ceiling body)) ≤ limit at bounded
      omega
    | some descriptor =>
      rcases descriptor with ⟨values,names,code,r1,r2⟩
      change max 0 (max (ceiling code) (ceiling body)) ≤ limit at bounded
      omega

theorem pushedCode {width : Nat} [NeZero width] {C F : Type}
    (source : WordSemStateFiniteExact width C F)
    (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) :
    (WordSemStateFiniteExact.pushEnv envs handler source).code = source.code := by
  rcases handler with _ | ⟨_,_,_,_⟩ <;> rfl

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.forgetSimulation
#print axioms InitECandidate.Solver.WordToStackBound.callHandlerSafe
#print axioms InitECandidate.Solver.WordToStackBound.pushedCode
