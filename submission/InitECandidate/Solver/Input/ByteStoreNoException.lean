import InitECandidate.Solver.Input.NoException

namespace InitECandidate.Solver.Input.NoException
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem store_byte (code) (address value : ExpHOL 64) : Safe code (.storeByte address value) := by
  intro source installed identifier payload
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | (solve | simp) | split

end InitECandidate.Solver.Input.NoException

#print axioms InitECandidate.Solver.Input.NoException.store_byte
