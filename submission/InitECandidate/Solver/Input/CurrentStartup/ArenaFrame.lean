import InitECandidate.Solver.Input.CurrentStartup.ArenaState
import InitECandidate.Solver.Input.MemoryMetadata

namespace InitECandidate.Solver.Input.CurrentStartup
open Flapjack PanSemStateFiniteExact

open Flapjack.Pancake.PanLang

/-- General execution facts needed by persistent helpers. Allocation
cursors are tracked separately by the particular caller's physical model. -/
structure Runtime (state : PanSemStateFiniteExact 64 Guest.HostMemory) : Prop where
  domain : state.memaddrs=InitE.ordinaryDomain
  code : OriginalCode.Installed state.code
  scalars : OriginalScalarGlobals.Scalars state.globals

def ArenaState.runtime {source : PanSemStateFiniteExact 64 Guest.HostMemory}
    (arena : ArenaState source) : Runtime source:=⟨arena.domain,arena.code,arena.scalars⟩

instance {source : PanSemStateFiniteExact 64 Guest.HostMemory} : Coe (ArenaState source) (Runtime source):=⟨ArenaState.runtime⟩

theorem Runtime.of_frame {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Runtime source) (frame : LocalEffects.erase post=LocalEffects.erase source) : Runtime post := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  have domain:=congrArg PanSemStateFiniteExact.memaddrs frame
  have code:=congrArg PanSemStateFiniteExact.code frame
  change post.globals=source.globals at globals
  change post.memaddrs=source.memaddrs at domain
  change post.code=source.code at code
  exact ⟨domain.trans data.domain,by rw [code]; exact data.code,by rw [globals]; exact data.scalars⟩

theorem Runtime.of_metadata {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : Runtime source) (frame : MemoryMetadata.erase post=MemoryMetadata.erase source) : Runtime post := by
  have globals:=congrArg PanSemStateFiniteExact.globals frame
  change post.globals=source.globals at globals
  exact ⟨(MemoryMetadata.domain frame).trans data.domain,by rw [MemoryMetadata.code frame]; exact data.code,
    by rw [globals]; exact data.scalars⟩

/-- Actual evaluation preserves the general runtime facts on every outcome.
No fixed value for a cursor global, heap result or later success is required. -/
theorem Runtime.after {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    {program : ProgHOL 64} {outcome : Option (PanSemResultExact 64)}
    (data : Runtime source) (run : evaluateHOLFiniteState source program=(outcome,post)) : Runtime post := by
  have fields:=evaluation_fields source post program outcome run
  exact ⟨fields.1.trans data.domain,by rw [fields.2.2.2]; exact data.code,data.scalars.after run⟩

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
    domain.trans data.domain,by rw [code]; exact data.code,by rw [globals]; exact data.scalars⟩

/-- Runtime metadata suffices for the initialized cursor invariant even
when temporary scratch bytes have changed. -/
theorem ArenaState.of_metadata {source post : PanSemStateFiniteExact 64 Guest.HostMemory}
    (data : ArenaState source) (frame : MemoryMetadata.erase post=MemoryMetadata.erase source) : ArenaState post := by
  have globals := congrArg PanSemStateFiniteExact.globals frame
  have domain := MemoryMetadata.domain frame
  have code := MemoryMetadata.code frame
  change post.globals=source.globals at globals
  exact ⟨by rw [globals]; exact data.scratch,by rw [globals]; exact data.frame,
    domain.trans data.domain,by rw [code]; exact data.code,by rw [globals]; exact data.scalars⟩

end InitECandidate.Solver.Input.CurrentStartup

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.of_frame

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.of_metadata

#print axioms InitECandidate.Solver.Input.CurrentStartup.ArenaState.runtime
#print axioms InitECandidate.Solver.Input.CurrentStartup.Runtime.of_frame
#print axioms InitECandidate.Solver.Input.CurrentStartup.Runtime.of_metadata
#print axioms InitECandidate.Solver.Input.CurrentStartup.Runtime.after
