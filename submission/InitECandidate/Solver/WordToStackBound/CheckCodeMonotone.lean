import InitECandidate.Solver.WordToStackBound.CheckCode

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

theorem entriesSafe_mono {width : Nat} [NeZero width] (small large : Nat)
    (entries : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (le : small ≤ large) (safe : entriesSafe small entries = true) :
    entriesSafe large entries = true := by
  apply List.all_eq_true.mpr
  intro entry member
  have checked := List.all_eq_true.mp safe entry member
  simp only [Bool.and_eq_true, decide_eq_true_eq] at checked ⊢
  exact ⟨checked.1, checked.2.trans le⟩

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.entriesSafe_mono
