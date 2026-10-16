import InitECandidate.Solver.LabBound.CheckLayout
import InitECandidate.Proofs.BackendStages.Padded713

/-! Resource pilot on the largest fixed Padded source module. -/
namespace InitECandidate.Solver.LabBound
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem padded713_fits :
    sectionFits 24 InitECandidate.Proofs.BackendStages.Padded713 = true := by
  decide

end InitECandidate.Solver.LabBound

#print axioms InitECandidate.Solver.LabBound.padded713_fits
