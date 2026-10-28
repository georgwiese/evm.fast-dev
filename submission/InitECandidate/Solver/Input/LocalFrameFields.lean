import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.LocalEffects
open Flapjack PanSemStateFiniteExact

/-- Project physical invariants before instantiating a long concrete store
state, so callers do not expand that state under the erased record. -/
theorem domain_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : erase target = erase source) :
    target.memaddrs = source.memaddrs := by
  have projected := congrArg PanSemStateFiniteExact.memaddrs frame
  exact projected

theorem endian_of_erase (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : erase target = erase source) :
    target.be = source.be := by
  have projected := congrArg PanSemStateFiniteExact.be frame
  exact projected

end InitECandidate.Solver.Input.LocalEffects

#print axioms InitECandidate.Solver.Input.LocalEffects.domain_of_erase
