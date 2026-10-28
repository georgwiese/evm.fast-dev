import InitECandidate.Solver.WitnessRadix.Memeq32
import InitECandidate.Solver.Input.LocalEffectsLoop

/-! Actual memeq physical frame, independent of dictionary loop costs. -/
namespace InitECandidate.Solver.MutableTable.MemeqAny
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix

set_option maxRecDepth 100000 in
theorem readonly (code) : Input.LocalEffects.Preserves code Memeq32.body := by
  simp only [Memeq32.body,Guest.guestFn_memeq,progToHOL,expToHOL,shapeToHOL,List.map_cons,List.map_nil]
  repeat first
    | apply Input.LocalEffects.declared
    | apply Input.LocalEffects.sequence
    | apply Input.LocalEffects.conditional
    | apply Input.LocalEffects.loop
    | exact Input.LocalEffects.assign code _ _
    | exact Input.LocalEffects.returned code _
    | exact Input.LocalEffects.skip code

end InitECandidate.Solver.MutableTable.MemeqAny

#print axioms InitECandidate.Solver.MutableTable.MemeqAny.readonly
