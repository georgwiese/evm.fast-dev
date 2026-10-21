import InitECandidate.Solver.Input.ConstructorRuntimeFrame

namespace InitECandidate.Solver.Input
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current scratch cursors follow from the actual returned arena and the
two named preserved globals, independently of the persistent heap advance. -/
theorem ConstructorRuntimeFrame.scratch (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (frame : ConstructorRuntimeFrame source target) (arena : Rlp.Validation.Arena source cursor limit) : Rlp.Validation.Arena target cursor limit :=
  ⟨frame.domain.trans arena.domain,(frame.globals _ (by decide) (by decide) (by decide)).trans arena.cursorGlobal,
    (frame.globals _ (by decide) (by decide) (by decide)).trans arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩

/-- Original hash helpers, host oracle and workspace pointers survive the
actual block-hash publications and both witness constructors. -/
theorem ConstructorRuntimeFrame.hash_environment (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64)
    (frame : ConstructorRuntimeFrame source target) (environment : Keccak256.Environment source stp pad) : Keccak256.Environment target stp pad := {
  domain := frame.domain.trans environment.domain
  stateGlobal := (frame.globals _ (by decide) (by decide) (by decide)).trans environment.stateGlobal
  scratchGlobal := (frame.globals _ (by decide) (by decide) (by decide)).trans environment.scratchGlobal
  zeroCode := by rw [frame.code]; exact environment.zeroCode
  copyCode := by rw [frame.code]; exact environment.copyCode
  hashCode := ⟨by rw [frame.code]; exact environment.hashCode.block,
    by rw [frame.code]; exact environment.hashCode.perm,frame.oracle.trans environment.hashCode.oracleEq⟩ }

end InitECandidate.Solver.Input

#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.scratch
#print axioms InitECandidate.Solver.Input.ConstructorRuntimeFrame.hash_environment
