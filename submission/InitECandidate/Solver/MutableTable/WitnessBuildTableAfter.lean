import InitECandidate.Solver.MutableTable.WitnessBuildOutputFields
import InitECandidate.Solver.MutableTable.BuildInvariantFrame32
import InitECandidate.Solver.Input.LocalEffects

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine later witness constructor preserves the entire earlier
database, including its arbitrary-collision placement/history. The actual
first returned heap supplies the separation, rather than an assumed gap. -/
theorem Normal.table_after_build
    (source middle nextSource target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice)
    (nextArray nextHeap : BitVec 64) (nextCount : Nat) (stp pad scratch : BitVec 64)
    (inputs : Inputs source array heap count maximum slices stp pad scratch)
    (first : Normal source middle array heap count stp pad scratch)
    (entryFrame : Input.LocalEffects.erase nextSource=Input.LocalEffects.erase middle)
    (nextHeapCell : nextSource.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)))
    (second : Normal nextSource target nextArray nextHeap nextCount stp pad scratch)
    (stateArena : AllocatedBytes.Arena stp 200) (padArena : AllocatedBytes.Arena pad 136) (scratchArena : AllocatedBytes.Arena scratch 32)
    (buffersBeforeHeap : stp.toNat+200≤heap.toNat ∧ pad.toNat+136≤heap.toNat ∧ scratch.toNat+32≤heap.toNat) :
    ∃ bits stored input logical,
      let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
      2≤bits ∧ bits≤32 ∧ 2^bits≤4*count+4 ∧ AllocatedLayout.Ready plan ∧
      Layout32.Built bits target plan scratch stored input logical ∧ History plan input ∧ input.length=count ∧
      plan.table+72+57*plan.capacity+plan.padding=nextHeap.toNat := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,built,history,length,ready,heapCell⟩ := first.table
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  have entryGlobals:=congrArg PanSemStateFiniteExact.globals entryFrame
  change nextSource.globals=middle.globals at entryGlobals
  have actualHeap : BitVec.ofNat 64 (plan.table+72+57*plan.capacity+plan.padding)=nextHeap := by
    rw [entryGlobals,heapCell] at nextHeapCell
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using nextHeapCell
  have frontier : plan.table+72+57*plan.capacity+plan.padding=nextHeap.toNat := by
    have number:=congrArg BitVec.toNat actualHeap
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by have h:=ready.fits; change plan.table+72+57*plan.capacity+plan.padding≤33806089496 at h; omega)] at number
    exact number
  have entryMemory:=Input.LocalEffects.memory_of_erase middle nextSource entryFrame
  have entryDomain:=congrArg PanSemStateFiniteExact.memaddrs entryFrame
  have entryEndian:=congrArg PanSemStateFiniteExact.be entryFrame
  have nextBuilt:=Layout32.built_fields middle nextSource plan bits scratch stored input logical entryMemory.symm entryDomain.symm entryEndian.symm built
  obtain ⟨code,domain,endian,exceptions,oracle,globals⟩ := second.fields nextSource target nextArray nextHeap nextCount stp pad scratch
  have before : stp.toNat+200≤plan.records ∧ pad.toNat+136≤plan.records ∧ scratch.toNat+32≤plan.records := by
    by_cases zero : count=0
    · simpa only [plan,Constructor.allocationPlan,effectiveRecords,zero,↓reduceIte] using buffersBeforeHeap
    · simpa only [plan,Constructor.allocationPlan,effectiveRecords,if_neg zero] using inputs.before zero
  have finalBuilt:=Layout32.built_preserved_by_later nextSource target plan ready nextHeap.toNat (by omega) stp pad scratch
    stateArena padArena scratchArena before domain.symm endian.symm
    (by intro query valid; exact second.memory query valid.2 valid.1) bits scratch stored input logical nextBuilt
  exact ⟨bits,stored,input,logical,lower,upper,capacity,ready,finalBuilt,history,length,frontier⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.table_after_build
