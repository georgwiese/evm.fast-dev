import InitECandidate.Solver.StackRemoveDirect.Safety
import InitECandidate.Solver.StackAllocBound.Safety
import InitECandidate.Proofs.BackendStages.Alloc64
import InitECandidate.Proofs.BackendStages.AllocStubs

/-! Actual fixed-code pilot: straight calls avoid label 6, whose installed
StoreConsts body is allowed to remain outside the certified reachable class. -/
namespace InitECandidate.Solver.StackRemoveDirect
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem raw64Eligible : InitECandidate.Solver.StackAllocBound.eligible raw64 = true := by decide

theorem alloc64Supported : supported Alloc64.2 = true := by decide

theorem allocStubsSupported :
    AllocStubs.all (fun entry => entry.1 == 6 || supported entry.2) = true := by decide

end InitECandidate.Solver.StackRemoveDirect
#print axioms InitECandidate.Solver.StackRemoveDirect.raw64Eligible
#print axioms InitECandidate.Solver.StackRemoveDirect.alloc64Supported
#print axioms InitECandidate.Solver.StackRemoveDirect.allocStubsSupported
