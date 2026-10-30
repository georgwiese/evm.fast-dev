import InitECandidate.Solver.Input.CurrentStartup.ArenaState
import InitECandidate.Solver.Input.MemoryMetadata

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack PanSemStateFiniteExact

/-- Pure local/clock changes retain both actual initialized arena cursors,
the fixed ordinary domain and current installed Software code. -/
theorem ArenaState.of_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : ArenaState source) (frame : LocalEffects.erase post=LocalEffects.erase source) : ArenaState post := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have code:=congrArg PanSemStateFiniteExact.code frame
  change post.globals=source.globals at globals
  change post.memaddrs=source.memaddrs at domain
  change post.code=source.code at code
  exact ⟨by rw [globals]; exact data.scratch,by rw [globals]; exact data.frame,
    domain.trans data.domain,by rw [code]; exact data.code⟩

/-- Runtime metadata suffices for the initialized cursor invariant even
when temporary scratch bytes have changed. -/
theorem ArenaState.of_metadata {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : ArenaState source) (frame : MemoryMetadata.erase post=MemoryMetadata.erase source) : ArenaState post := by
  have globals := congrArg PanSemStateFiniteExact.globals frame
  have domain := MemoryMetadata.domain frame
  have code := MemoryMetadata.code frame
  change post.globals=source.globals at globals
  exact ⟨by rw [globals]; exact data.scratch,by rw [globals]; exact data.frame,
    domain.trans data.domain,by rw [code]; exact data.code⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.of_frame

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.of_metadata
