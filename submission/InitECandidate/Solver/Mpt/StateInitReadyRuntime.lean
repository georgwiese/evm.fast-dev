import InitECandidate.Solver.Mpt.StateInitDatabase
import InitECandidate.Solver.Input.OriginalScalarGlobals
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.StateInit
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

set_option maxRecDepth 100000 in
open scoped InitE.MetadataComputation InitE.NameComputation in
theorem workspace_name : ofString "ws"∈Input.OriginalScalarGlobals.names := by decide_cbv

/-- The true workspace/heap updates retain all original scalar-global types. -/
theorem ready_scalars (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes : BitVec 64)
    (scalars : Input.OriginalScalarGlobals.Scalars source.globals) : Input.OriginalScalarGlobals.Scalars (ready source heap nodes root codes).globals :=
  (scalars.update (ofString "heap_ptr") (PersistentAlloc.rounded heap 40#64)).update (ofString "ws") heap

/-- Persistent workspace initialization retains the actual scratch arena. -/
theorem ready_scratch (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) : Rlp.Validation.Arena (ready source heap nodes root codes) cursor limit := by
  have fields:=ready_fields source heap nodes root codes
  exact ⟨arena.domain,(fields.2.2.2 _ (by decide) (by decide)).trans arena.cursorGlobal,
    (fields.2.2.2 _ (by decide) (by decide)).trans arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩

/-- The original hash helpers, oracle and both real hash-workspace pointers
remain available after the actual initialized40-byte workspace prefix. -/
theorem ready_environment (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap nodes root codes stp pad : BitVec 64)
    (environment : Keccak256.Environment source stp pad) : Keccak256.Environment (ready source heap nodes root codes) stp pad := by
  have fields:=ready_fields source heap nodes root codes
  exact ⟨environment.domain,(fields.2.2.2 _ (by decide) (by decide)).trans environment.stateGlobal,
    (fields.2.2.2 _ (by decide) (by decide)).trans environment.scratchGlobal,
    environment.zeroCode,environment.copyCode,⟨environment.hashCode.block,environment.hashCode.perm,environment.hashCode.oracleEq⟩⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.workspace_name
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_scalars
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_scratch
#print axioms InitECandidate.Solver.Mpt.StateInit.ready_environment
