import InitECandidate.Solver.Input.ClockCost

namespace InitECandidate.Solver.Input
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact

theorem QuietClock.store_byte (code) (address value : ExpHOL 64) : QuietClock.Preserves code (.storeByte address value) := by
  intro source installed
  rw [evaluateHOLFiniteState_storeByte]
  repeat first | rfl | split

theorem ClockCost.store_byte (code) (address value : ExpHOL 64) : ClockCost.Bound code (.storeByte address value) 0 :=
  ClockCost.of_quiet code _ (QuietClock.store_byte code address value)

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.QuietClock.store_byte
#print axioms InitECandidate.Solver.Input.ClockCost.store_byte
