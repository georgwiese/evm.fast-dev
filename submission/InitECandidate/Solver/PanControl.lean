import InitECandidate.Solver.PanState

namespace InitECandidate.Solver.WitnessRadix.BackingLayout
open Flapjack PanSemStateFiniteExact

def control {F : Type} (state : PanSemStateFiniteExact 64 F) : PanSemStateFiniteExact 64 F :=
  emptyLocalsHOLFinite { state with memory := fun _ => .word 0#64, clock := 0 }

theorem control_of_frame {F : Type} (source target : PanSemStateFiniteExact 64 F)
    (frame : emptyLocalsHOLFinite source = emptyLocalsHOLFinite target) : control source = control target := by
  have updated := congrArg (fun state : PanSemStateFiniteExact 64 F =>
    { state with memory := fun _ => .word 0#64, clock := 0 }) frame
  simpa only [control, emptyLocalsHOLFinite] using updated

end InitECandidate.Solver.WitnessRadix.BackingLayout

#print axioms InitECandidate.Solver.WitnessRadix.BackingLayout.control_of_frame
