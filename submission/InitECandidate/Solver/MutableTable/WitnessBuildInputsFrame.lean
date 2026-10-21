import InitECandidate.Solver.MutableTable.WitnessBuildInputsAfter

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Transport caller inputs through real local/clock-only wrapper changes. -/
theorem Inputs.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) (actual : Inputs source array heap count maximum slices stp pad scratch)
    (code : target.code=source.code) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (oracle : target.ffi.oracle=source.ffi.oracle) (globals : target.globals=source.globals) (memory : target.memory=source.memory) :
    Inputs target array heap count maximum slices stp pad scratch := by
  refine ⟨by rw [code]; exact actual.installed,
    Keccak256.Environment.of_fields source target stp pad actual.environment domain code oracle (by intro key other; rw [globals]),
    by rw [globals]; exact actual.scratchGlobal,endian.trans actual.little,by rw [globals]; exact actual.heapGlobal,
    actual.heapLower,actual.heapAligned,actual.room,actual.records,?_,?_,actual.buffers,actual.before,actual.scratchAligned,actual.sizes,actual.sourceLower,actual.sourceBefore,actual.heapAfterScratch⟩
  · intro index inside
    rw [memory]
    exact actual.pointers index inside
  · intro index inside
    rw [memory]
    exact actual.lengths index inside

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.of_fields
