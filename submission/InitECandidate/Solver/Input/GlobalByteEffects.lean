import InitECandidate.Solver.Input.GlobalEffectsAtoms

namespace InitECandidate.Solver.Input.GlobalEffects
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

/-- A literal byte store can change memory or fail, and preserves every
global and the code table on all outcomes. -/
theorem byte_store (key : MlS) (code) (address value : ExpHOL 64) : Preserves key code (.storeByte address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

end InitECandidate.Solver.Input.GlobalEffects

#print axioms InitECandidate.Solver.Input.GlobalEffects.byte_store
