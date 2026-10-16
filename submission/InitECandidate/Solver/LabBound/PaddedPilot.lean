import InitECandidate.Solver.LabBound.CheckLayout
import InitECandidate.Proofs.BackendStages.Padded64

/-! A pilot of the syntax checker on a fixed baseline target section. This is
one section only, not the layout certificate for the whole guest. -/
namespace InitECandidate.Solver.LabBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem padded64_fits :
    sectionFits 24 InitECandidate.Proofs.BackendStages.Padded64 = true := by
  decide

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.padded64_fits
