import InitECandidate.Solver.StackAllocBound.Safety

namespace InitECandidate.Solver.StackAllocBound
open Flapjack Flapjack.Compiler.Backend.StackLang

theorem list_codeSafe {width : Nat} [NeZero width]
    (entries : List (Nat × HolProg width))
    (safe : entries.all (fun entry => eligible entry.2) = true) : CodeSafe (sptFromAList entries) := by
  intro key p lookup
  rw [sptLookup_sptFromAList] at lookup
  exact List.all_eq_true.mp safe (key, p) (sptAListLookup_mem key entries p lookup)

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.list_codeSafe
