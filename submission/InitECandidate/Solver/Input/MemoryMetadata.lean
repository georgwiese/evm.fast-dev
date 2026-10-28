import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.Input.MemoryMetadata
open Flapjack PanSemStateFiniteExact

/-- All physical fields except memory, locals and clock. -/
def erase (source : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  emptyLocalsHOLFinite {source with memory := fun _ => .word 0#64,clock := 0}

theorem domain {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.memaddrs = source.memaddrs := by
  have projected := congrArg PanSemStateFiniteExact.memaddrs frame
  exact projected

theorem endian {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.be = source.be := by
  have projected := congrArg PanSemStateFiniteExact.be frame
  exact projected

theorem code {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : erase target = erase source) :
    target.code = source.code := by
  have projected := congrArg PanSemStateFiniteExact.code frame
  exact projected

theorem of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} (frame : LocalEffects.erase target = LocalEffects.erase source) :
    erase target = erase source := by
  have projected := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with memory := fun _ => .word 0#64}) frame
  exact projected

end InitECandidate.Solver.Input.MemoryMetadata

#print axioms InitECandidate.Solver.Input.MemoryMetadata.domain
#print axioms InitECandidate.Solver.Input.MemoryMetadata.endian
