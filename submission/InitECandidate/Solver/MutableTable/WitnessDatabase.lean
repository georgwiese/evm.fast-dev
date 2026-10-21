import InitECandidate.Solver.MutableTable.WitnessBuildReturnedRecords
import InitECandidate.Solver.MutableTable.WitnessBuildTableAfter
import InitECandidate.Solver.MutableTable.WitnessPriorRecordsFrame

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- A physical immutable witness database derived from the original
constructor. The input history permits duplicate keys and arbitrary hashes. -/
structure Database (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array table : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (scratch : BitVec 64) : Prop where
  domain : source.memaddrs=InitE.ordinaryDomain
  little : source.be=false
  sizes : ∀ index<count,(slices index).2.toNat≤maximum
  data : ∃ bits stored input logical,
    let plan:=Constructor.allocationPlan (effectiveRecords array table count) table.toNat count (2^bits)
    2≤bits ∧ bits≤32 ∧ 2^bits≤4*count+4 ∧ AllocatedLayout.Ready plan ∧
    Layout32.Built bits source plan scratch stored input logical ∧ History plan input ∧ input.length=count ∧ Records source plan slices
  arenas : ∀ index<count,AllocatedBytes.Arena (slices index).1 (slices index).2.toNat
  sourceLower : ∀ index<count,2713731432≤(slices index).1.toNat
  sourceBefore : ∀ index<count,(slices index).1.toNat+(slices index).2.toNat≤table.toNat

/-- Every genuine constructor return supplies the complete lookup context,
including real slice records and the original per-record size bound. -/
theorem Normal.database (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64)
    (inputs : Inputs source array heap count maximum slices stp pad scratch) (actual : Normal source target array heap count stp pad scratch) :
    Database target array heap count maximum slices scratch := by
  obtain ⟨code,domain,endian,exceptions,oracle,globals⟩ := actual.fields source target array heap count stp pad scratch
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,built,history,length,ready,heapCell⟩ := actual.table
  exact ⟨domain.trans inputs.environment.domain,endian.trans inputs.little,inputs.sizes,
    ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,inputs.returned_records source target array heap count maximum slices stp pad scratch actual bits ready⟩,
    fun index inside=>(inputs.buffers index inside).inputArena,inputs.sourceLower,inputs.sourceBefore⟩

/-- Building the second original database retains the complete first
database at the real current state, with its genuine slice outputs. -/
theorem Normal.database_after_build
    (source middle nextSource target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice)
    (nextArray nextHeap : BitVec 64) (nextCount : Nat) (stp pad scratch : BitVec 64)
    (inputs : Inputs source array heap count maximum slices stp pad scratch)
    (first : Normal source middle array heap count stp pad scratch)
    (entryFrame : Input.LocalEffects.erase nextSource=Input.LocalEffects.erase middle)
    (nextHeapCell : nextSource.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word nextHeap)))
    (second : Normal nextSource target nextArray nextHeap nextCount stp pad scratch)
    (stateArena : AllocatedBytes.Arena stp 200) (padArena : AllocatedBytes.Arena pad 136) (scratchArena : AllocatedBytes.Arena scratch 32)
    (buffersBeforeHeap : stp.toNat+200≤heap.toNat ∧ pad.toNat+136≤heap.toNat ∧ scratch.toNat+32≤heap.toNat) :
    Database target array heap count maximum slices scratch := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,frontier⟩ :=
    first.table_after_build source middle nextSource target array heap count maximum slices nextArray nextHeap nextCount stp pad scratch inputs entryFrame nextHeapCell second
      stateArena padArena scratchArena buffersBeforeHeap
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  change plan.table+72+57*plan.capacity+plan.padding=nextHeap.toNat at frontier
  have rows:=inputs.returned_records source middle array heap count maximum slices stp pad scratch first bits ready
  have memory:=Input.LocalEffects.memory_of_erase middle nextSource entryFrame
  have entryRows : Records nextSource plan slices :=
    ⟨by intro i inside; exact (congrFun memory _).trans (rows.pointers i inside),
      by intro i inside; exact (congrFun memory _).trans (rows.lengths i inside)⟩
  have before : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ scratch.toNat+32≤plan.records := by
    by_cases zero : count=0
    · simpa only [plan,Constructor.allocationPlan,effectiveRecords,zero,↓reduceIte] using buffersBeforeHeap
    · simpa only [plan,Constructor.allocationPlan,effectiveRecords,if_neg zero] using inputs.before zero
  have finalRows:=prior_records_preserved nextSource target plan ready nextHeap.toNat (Nat.le_of_eq frontier) stp pad scratch stateArena padArena scratchArena before
    (by intro query kept; exact second.memory query kept.2 kept.1) slices entryRows
  have firstFields:=first.fields source middle array heap count stp pad scratch
  have secondFields:=second.fields nextSource target nextArray nextHeap nextCount stp pad scratch
  have entryDomain:=congrArg PanSemStateFiniteExact.memaddrs entryFrame
  have entryEndian:=congrArg PanSemStateFiniteExact.be entryFrame
  exact ⟨secondFields.2.1.trans (entryDomain.trans (firstFields.2.1.trans inputs.environment.domain)),
    secondFields.2.2.1.trans (entryEndian.trans (firstFields.2.2.1.trans inputs.little)),inputs.sizes,
    ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,finalRows⟩,
    fun index inside=>(inputs.buffers index inside).inputArena,inputs.sourceLower,inputs.sourceBefore⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.database
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.database_after_build
