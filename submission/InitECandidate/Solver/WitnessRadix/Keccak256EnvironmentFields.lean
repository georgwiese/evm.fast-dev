import InitECandidate.Solver.WitnessRadix.Keccak256Allocated
import InitECandidate.Solver.Input.EvaluationOracle
import InitECandidate.Solver.PanHeapGlobals

namespace InitECandidate.Solver.WitnessRadix.Keccak256
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The hash environment depends on two globals and immutable evaluator
fields. Its oracle function survives real external calls as well. -/
theorem Environment.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64)
    (environment : Environment source stp pad) (domain : target.memaddrs=source.memaddrs) (code : target.code=source.code)
    (oracle : target.ffi.oracle=source.ffi.oracle) (globals : HeapGlobals source target) : Environment target stp pad := {
  domain := domain.trans environment.domain
  stateGlobal := (globals _ (by decide)).trans environment.stateGlobal
  scratchGlobal := (globals _ (by decide)).trans environment.scratchGlobal
  zeroCode := by rw [code]; exact environment.zeroCode
  copyCode := by rw [code]; exact environment.copyCode
  hashCode := ⟨by rw [code]; exact environment.hashCode.block,by rw [code]; exact environment.hashCode.perm,oracle.trans environment.hashCode.oracleEq⟩ }

theorem Environment.after_execution (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (stp pad : BitVec 64)
    (environment : Environment source stp pad) (program : ProgHOL 64) (result : Option (PanSemResultExact 64))
    (run : evaluateHOLFiniteState source program=(result,target)) (globals : HeapGlobals source target) : Environment target stp pad :=
  Environment.of_fields source target stp pad environment (Input.evaluation_fields source target program result run).1
    (Input.evaluation_fields source target program result run).2.2.2 (Input.evaluation_oracle source target program result run) globals

end InitECandidate.Solver.WitnessRadix.Keccak256

#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Environment.of_fields
#print axioms InitECandidate.Solver.WitnessRadix.Keccak256.Environment.after_execution
