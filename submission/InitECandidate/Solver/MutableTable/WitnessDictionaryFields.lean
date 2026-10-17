import InitECandidate.Solver.MutableTable.WitnessDictionaryPair

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Caller-local binding/restoration and clock changes preserve both dictionary
models. Only their real memory, mapping and endian fields are relevant. -/
theorem DictionaryPair.of_fields (left right leftNext rightNext : PanSemStateFiniteExact 64 Guest.HostMemory)
    {records table count : Nat} (observation : DictionaryObservation records table count)
    (sliceFor : BitVec 64 → Graph.Slice) (scratch : BitVec 64)
    (leftMemory : left.memory=leftNext.memory) (rightMemory : right.memory=rightNext.memory)
    (leftDomain : left.memaddrs=leftNext.memaddrs) (rightDomain : right.memaddrs=rightNext.memaddrs)
    (leftEndian : left.be=leftNext.be) (rightEndian : right.be=rightNext.be)
    (pair : DictionaryPair left right observation sliceFor scratch) : DictionaryPair leftNext rightNext observation sliceFor scratch := by
  have built:=Layout32.built_fields left leftNext observation.plan observation.bits scratch observation.distinctCount
    observation.input observation.logical leftMemory leftDomain leftEndian pair.built
  have records : Records leftNext observation.plan (fun index=>sliceFor (BitVec.ofNat 64 index)) := by
    constructor
    · intro index inside;rw [←leftMemory];exact pair.records.pointers index inside
    · intro index inside;rw [←leftMemory];exact pair.records.lengths index inside
  have mapped : rightNext.memaddrs (BackingLayout.cell (AllocatedLayout.layout observation.plan) .header 24) := by
    rw [←rightDomain];exact pair.rootMapped
  have word : rightNext.memory (BackingLayout.cell (AllocatedLayout.layout observation.plan) .header 24)=.word observation.root := by
    rw [←rightMemory];exact pair.rootWord
  refine ⟨pair.bitsLow,pair.bitsTop,pair.ready,built,pair.history,pair.matching,pair.length,records,mapped,word,
    QueryMemory.represents_of_fields right rightNext rightMemory rightDomain rightEndian _ _ _ observation.root _ pair.represented,?_⟩
  intro query read
  exact pair.support query ((QueryMemory.reads_stable right rightNext _ _ _ observation.root
    (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals count))
    (by intro address member;exact congrFun rightMemory address) query).mpr read)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.DictionaryPair.of_fields
