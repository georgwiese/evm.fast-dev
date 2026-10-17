import InitECandidate.Solver.WitnessRadix.ConstructorPlan
import InitECandidate.Solver.MutableTable.BuildInvariantFrame32
import InitECandidate.Solver.MutableTable.WitnessPriorRadixFrame
import InitECandidate.Solver.MutableTable.WitnessPriorRecordsFrame
import InitECandidate.Solver.MutableTable.WitnessBuildKeyHistory

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The common observed dictionary from one pair of actual constructors. -/
structure DictionaryObservation (records table count : Nat) where
  bits : Nat
  distinctCount : Nat
  input : List (Find.Key32×BitVec 64)
  logical : Find.Model32 (BitVec 64)
  keyFor : BitVec 64 → ByteKeys.Key
  root : BitVec 64

def DictionaryObservation.plan {records table count : Nat} (observation : DictionaryObservation records table count) : AllocatedLayout.Plan:=
  Constructor.allocationPlan records table count (2^observation.bits)

def DictionaryObservation.heapEnd {records table count : Nat} (observation : DictionaryObservation records table count) : Nat:=
  observation.plan.table+72+57*observation.plan.capacity+observation.plan.padding

/-- A reusable state relation for one initialized immutable witness map.
The original physical hash map and candidate radix map share their observed
last-record-wins dictionary while retaining separate private memory. -/
structure DictionaryPair (left right : PanSemStateFiniteExact 64 Guest.HostMemory)
    {records table count : Nat} (observation : DictionaryObservation records table count)
    (sliceFor : BitVec 64 → Graph.Slice) (scratch : BitVec 64) : Prop where
  bitsLow : 2≤observation.bits
  bitsTop : observation.bits≤32
  ready : AllocatedLayout.Ready observation.plan
  built : Layout32.Built observation.bits left observation.plan scratch observation.distinctCount observation.input observation.logical
  history : History observation.plan observation.input
  matching : KeysMatch observation.plan observation.keyFor observation.input
  length : observation.input.length=count
  records : Records left observation.plan (fun index=>sliceFor (BitVec.ofNat 64 index))
  rootMapped : right.memaddrs (BackingLayout.cell (AllocatedLayout.layout observation.plan) .header 24)
  rootWord : right.memory (BackingLayout.cell (AllocatedLayout.layout observation.plan) .header 24)=.word observation.root
  represented : QueryMemory.Represents right (AllocatedLayout.layout observation.plan).table (AllocatedLayout.layout observation.plan).keys
    (AllocatedLayout.layout observation.plan).vals observation.root
    (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals count))
  support : ∀ query,QueryMemory.reads right (AllocatedLayout.layout observation.plan).table (AllocatedLayout.layout observation.plan).keys
    (AllocatedLayout.layout observation.plan).vals observation.root
    (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals count)) query →
    BackingLayout.Protected (AllocatedLayout.layout observation.plan) count query

/-- Both complete dictionary models survive a later pair of constructors from
its actual own safe-memory frames and real allocation ordering. -/
theorem DictionaryPair.preserved_by_later (left right leftNext rightNext : PanSemStateFiniteExact 64 Guest.HostMemory)
    {records table count : Nat} (observation : DictionaryObservation records table count)
    (sliceFor : BitVec 64 → Graph.Slice) (scratch : BitVec 64) (pair : DictionaryPair left right observation sliceFor scratch)
    (nextTable : Nat) (before : observation.heapEnd≤nextTable) (stp pad out : BitVec 64)
    (stateArena : AllocatedBytes.Arena stp 200) (paddingArena : AllocatedBytes.Arena pad 136) (outputArena : AllocatedBytes.Arena out 32)
    (buffersBefore : stp.toNat+200≤records ∧ pad.toNat+136≤records ∧ out.toNat+32≤records)
    (leftDomain : left.memaddrs=leftNext.memaddrs) (rightDomain : right.memaddrs=rightNext.memaddrs)
    (leftEndian : left.be=leftNext.be) (rightEndian : right.be=rightNext.be)
    (leftFrame : ∀ query,query.toNat<nextTable ∧ Keccak256.Protected stp pad out query → leftNext.memory query=left.memory query)
    (rightFrame : ∀ query,query.toNat<nextTable ∧ Keccak256.Protected stp pad out query → rightNext.memory query=right.memory query) :
    DictionaryPair leftNext rightNext observation sliceFor scratch := by
  have nextBuilt:=Layout32.built_preserved_by_later left leftNext observation.plan pair.ready nextTable before stp pad out
    stateArena paddingArena outputArena buffersBefore leftDomain leftEndian leftFrame observation.bits scratch observation.distinctCount
    observation.input observation.logical pair.built
  have nextRecords:=prior_records_preserved left leftNext observation.plan pair.ready nextTable before stp pad out
    stateArena paddingArena outputArena buffersBefore leftFrame _ pair.records
  obtain ⟨mapped,word,represented,support⟩:=prior_radix_preserved right rightNext observation.plan pair.ready nextTable before stp pad out
    stateArena paddingArena outputArena buffersBefore rightDomain rightEndian observation.root
    (BackingLayout.initialTree observation.keyFor sliceFor (BackingLayout.ordinals count)) pair.rootMapped pair.rootWord pair.represented pair.support rightFrame
  exact ⟨pair.bitsLow,pair.bitsTop,pair.ready,nextBuilt,pair.history,pair.matching,pair.length,nextRecords,mapped,word,represented,support⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.DictionaryPair.preserved_by_later
