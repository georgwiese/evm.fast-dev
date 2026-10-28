import InitECandidate.Solver.Input.CurrentHash.ProgressiveProgram
import InitECandidate.Solver.Input.MerkleGlobals

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- All actual step outcomes retain each initialized nonheap global. -/
theorem step_globals (key : MlS) (code) (installed : OriginalCode.Installed code) (other : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code step := by
  rw [loop_shape.2]
  unfold afterCount capGuard afterCap updates
  apply GlobalEffects.declared
  apply GlobalEffects.sequence
  · exact GlobalEffects.conditional key code _ _ _ (GlobalEffects.assign key code _ _) (GlobalEffects.skip key code)
  · apply GlobalEffects.sequence
    · exact GlobalEffects.call_body key code (some none) (ofString "merkleize") arguments Merkle.formals Merkle.body .one (Merkle.original_code code installed) (Merkle.globals key code installed other)
    · exact GlobalEffects.sequence key code _ _ (GlobalEffects.assign key code _ _) (GlobalEffects.sequence key code _ _ (GlobalEffects.assign key code _ _) (GlobalEffects.assign key code _ _))

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.step_globals
