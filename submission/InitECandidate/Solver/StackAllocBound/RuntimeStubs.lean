import InitECandidate.Solver.StackAllocBound.Safety
import InitECandidate.Proofs.BackendStages.RawStubs

/-! Kernel-checked eligibility of the actual fixed runtime stubs. In particular,
the StoreConsts body at label 6 is admitted because its optional stub is none. -/
namespace InitECandidate.Solver.StackAllocBound

theorem rawStubsEligible :
    InitECandidate.Proofs.BackendStages.RawStubs.all (fun entry => eligible entry.2) = true := by
  decide

end InitECandidate.Solver.StackAllocBound
#print axioms InitECandidate.Solver.StackAllocBound.rawStubsEligible
