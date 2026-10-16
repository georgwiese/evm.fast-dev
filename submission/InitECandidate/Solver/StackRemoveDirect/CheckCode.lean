import InitECandidate.Solver.StackRemoveDirect.Safety

/-! Turn a decidable list check into the invariant on actual sparse-tree
lookups; label 6 remains unrestricted because every reachable call avoids it. -/
namespace InitECandidate.Solver.StackRemoveDirect
open Flapjack Flapjack.Compiler.Backend.StackLang

def entriesSafe {width : Nat} [NeZero width] (entries : List (Nat × HolProg width)) : Bool :=
  entries.all (fun entry => entry.1 == 6 || supported entry.2)

theorem entriesSafe_codeSafe {width : Nat} [NeZero width]
    (entries : List (Nat × HolProg width)) (safe : entriesSafe entries = true) :
    CodeSafe (sptFromAList entries) := by
  intro key p allowed lookup
  rw [sptLookup_sptFromAList] at lookup
  have member := sptAListLookup_mem key entries p lookup
  have good := List.all_eq_true.mp safe (key, p) member
  simpa [allowed] using good

end InitECandidate.Solver.StackRemoveDirect
#print axioms InitECandidate.Solver.StackRemoveDirect.entriesSafe_codeSafe
