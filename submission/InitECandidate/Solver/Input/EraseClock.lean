import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack PanSemStateFiniteExact

theorem same_clock {source target : PanSemStateFiniteExact 64 Guest.HostMemory}
    (fields : erase target = erase source) (clock : target.clock = source.clock) :
    emptyLocalsHOLFinite target = emptyLocalsHOLFinite source := by
  have reset := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with clock := target.clock}) fields
  change emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := target.clock} at reset
  rw [clock] at reset
  exact reset

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.same_clock
