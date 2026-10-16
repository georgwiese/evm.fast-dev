import InitECandidate.Solver.WordToStackBound.Cost

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

theorem popEnvCode {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width C F)
    (pop : WordSemStateFiniteExact.popEnv source = some post) : post.code = source.code := by
  unfold WordSemStateFiniteExact.popEnv at pop
  split at pop <;> cases pop <;> rfl

theorem callReturnSafe {width : Nat} [NeZero width] (limit : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (body : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (supported : noInstallSubprogsHOL (.call (some (values,names,body,l1,l2)) dest args handler) = true)
    (bounded : ceiling (.call (some (values,names,body,l1,l2)) dest args handler) ≤ limit) :
    noInstallSubprogsHOL body = true ∧ ceiling body ≤ limit := by
  constructor
  · cases handler with
    | none => simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using supported
    | some descriptor =>
      rcases descriptor with ⟨register,code,h1,h2⟩
      simp only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp,
        Bool.true_and, Bool.and_eq_true] at supported
      exact supported.1
  · cases handler with
    | none =>
      change max 0 (max (ceiling body) 0) ≤ limit at bounded
      omega
    | some descriptor =>
      rcases descriptor with ⟨register,code,h1,h2⟩
      change max 0 (max (ceiling body) (ceiling code)) ≤ limit at bounded
      omega

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.popEnvCode
#print axioms InitECandidate.Solver.WordToStackBound.callReturnSafe
