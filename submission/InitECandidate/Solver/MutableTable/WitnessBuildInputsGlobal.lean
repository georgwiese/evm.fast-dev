import InitECandidate.Solver.MutableTable.WitnessBuildInputsFrame
import InitECandidate.Solver.Input.GlobalAssign

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Publishing block context leaves the witness-constructor runtime and
physical inputs current when it touches none of their four pointer globals. -/
theorem Inputs.put_global (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (name : String) (word : BitVec 64)
    (different : ofString name≠ofString "heap_ptr" ∧ ofString name≠ofString "keccak_st" ∧ ofString name≠ofString "keccak_pad" ∧ ofString name≠ofString "mpt_hash_scratch") :
    Inputs (Input.putGlobal source name word) array heap count maximum slices stp pad scratch := by
  have environment : Keccak256.Environment (Input.putGlobal source name word) stp pad :=
    ⟨actual.environment.domain,
      (Input.putGlobal.lookup_other source name word _ (Ne.symm different.2.1)).trans actual.environment.stateGlobal,
      (Input.putGlobal.lookup_other source name word _ (Ne.symm different.2.2.1)).trans actual.environment.scratchGlobal,
      actual.environment.zeroCode,actual.environment.copyCode,
      ⟨actual.environment.hashCode.block,actual.environment.hashCode.perm,actual.environment.hashCode.oracleEq⟩⟩
  exact ⟨actual.installed,environment,
    (Input.putGlobal.lookup_other source name word _ (Ne.symm different.2.2.2)).trans actual.scratchGlobal,actual.little,
    (Input.putGlobal.lookup_other source name word _ (Ne.symm different.1)).trans actual.heapGlobal,
    actual.heapLower,actual.heapAligned,actual.room,actual.records,actual.pointers,actual.lengths,actual.buffers,actual.before,actual.scratchAligned,actual.sizes,actual.sourceLower,actual.sourceBefore,actual.heapAfterScratch⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.put_global
