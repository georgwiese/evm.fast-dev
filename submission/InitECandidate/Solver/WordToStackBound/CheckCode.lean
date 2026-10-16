import InitECandidate.Solver.WordToStackBound.Cost

namespace InitECandidate.Solver.WordToStackBound
open Flapjack

def entriesSafe {width : Nat} [NeZero width] (limit : Nat)
    (entries : List (Nat × Nat × WordLangProgHOL (BitVec width))) : Bool :=
  entries.all fun entry => noInstallSubprogsHOL entry.2.2 && decide (ceiling entry.2.2 ≤ limit)

theorem entriesSafe_codeSafe {width : Nat} [NeZero width] (limit : Nat)
    (entries : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (safe : entriesSafe limit entries = true) : CodeSafe limit (sptFromAList entries) := by
  have entrySafe : ∀ key arity program,
      sptLookup key (sptFromAList entries) = some (arity, program) →
      noInstallSubprogsHOL program = true ∧ ceiling program ≤ limit := by
    intro key arity program lookup
    rw [sptLookup_sptFromAList] at lookup
    have member := sptAListLookup_mem key entries (arity, program) lookup
    have checked := List.all_eq_true.mp safe (key, arity, program) member
    simpa only [Bool.and_eq_true, decide_eq_true_eq] using checked
  exact ⟨fun key arity program lookup => (entrySafe key arity program lookup).1,
    fun key arity program lookup => (entrySafe key arity program lookup).2⟩

end InitECandidate.Solver.WordToStackBound
#print axioms InitECandidate.Solver.WordToStackBound.entriesSafe_codeSafe
