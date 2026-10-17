import InitECandidate.Solver.MutableTable.WitnessEntryEnvironment
import InitECandidate.Solver.WitnessRadix.ConstructorPreparedContext

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

theorem EntryEnvironment.of_control (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (stp pad scratch : BitVec 64) (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl source)
    (entry : EntryEnvironment source stp pad scratch) : EntryEnvironment target stp pad scratch := by
  have globals : target.globals=source.globals:=congrArg (fun state=>state.globals) control
  have codes : target.code=source.code:=congrArg (fun state=>state.code) control
  have endian : target.be=source.be:=congrArg (fun state=>state.be) control
  refine ⟨?_,?_,Keccak256.Environment.of_control source target stp pad control entry.environment,entry.aligned,
    endian.trans entry.little,?_,?_,?_,?_,?_,?_⟩
  · rw [globals];exact entry.global
  · rw [codes];exact entry.keccakCode
  · rw [codes];exact entry.hashCode
  · rw [codes];exact entry.copyCode
  · rw [codes];exact entry.insertCode
  · rw [codes];exact entry.memeqCode
  · rw [codes];exact entry.findCode
  · rw [codes];exact entry.setCode

/-- The first constructor's exact cursor update preserves all fixed code/hash
metadata required by the second decoded witness map, including count zero. -/
theorem EntryEnvironment.after_constructor (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (allocation : AllocatedLayout.Plan) (stp pad scratch : BitVec 64)
    (control : KeccakAbsorb.hashControl target=KeccakAbsorb.hashControl (Constructor.preparedState source allocation))
    (entry : EntryEnvironment source stp pad scratch) : EntryEnvironment target stp pad scratch := by
  have prepared : EntryEnvironment (Constructor.preparedState source allocation) stp pad scratch:=
    ⟨(Constructor.prepared_global_other source allocation (ofString "mpt_hash_scratch") (by decide)).trans entry.global,
      entry.keccakCode,Constructor.prepared_environment source allocation stp pad entry.environment,entry.aligned,entry.little,
      entry.hashCode,entry.copyCode,entry.insertCode,entry.memeqCode,entry.findCode,entry.setCode⟩
  exact EntryEnvironment.of_control _ target stp pad scratch control prepared

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.EntryEnvironment.of_control
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.EntryEnvironment.after_constructor
