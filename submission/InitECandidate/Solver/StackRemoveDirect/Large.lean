import InitECandidate.Solver.StackRemoveDirect.Safety
import InitECandidate.Solver.StackAllocBound.Safety
import InitECandidate.Proofs.BackendStages.Alloc713

/-! Larger fixed-code pilot for the measured largest padded procedure. This
checks actual imported ASTs; no native computation or reimplemented literals. -/
namespace InitECandidate.Solver.StackRemoveDirect
open InitECandidate.Proofs.BackendStages
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem raw713Eligible : InitECandidate.Solver.StackAllocBound.eligible raw713 = true := by decide

theorem alloc713Supported : supported Alloc713.2 = true := by decide

end InitECandidate.Solver.StackRemoveDirect
#print axioms InitECandidate.Solver.StackRemoveDirect.raw713Eligible
#print axioms InitECandidate.Solver.StackRemoveDirect.alloc713Supported
