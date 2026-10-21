import InitECandidate.Solver.MutableTable.WitnessDatabaseBefore

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Both physical immutable tables lie before the genuine returned heap of
the second constructor. Its real entry heap identifies the first frontier. -/
theorem Normal.before_after_build
    (source middle nextSource target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice)
    (nextArray nextHeap : BitVec 64) (nextCount : Nat) (stp pad scratch : BitVec 64)
    (inputs : Inputs source array heap count maximum slices stp pad scratch)
    (first : Normal source middle array heap count stp pad scratch)
    (entryFrame : Input.LocalEffects.erase nextSource=Input.LocalEffects.erase middle)
    (second : Normal nextSource target nextArray nextHeap nextCount stp pad scratch)
    (stateArena : AllocatedBytes.Arena stp 200) (padArena : AllocatedBytes.Arena pad 136) (scratchArena : AllocatedBytes.Arena scratch 32)
    (buffersBeforeHeap : stp.toNat+200≤heap.toNat ∧ pad.toNat+136≤heap.toNat ∧ scratch.toNat+32≤heap.toNat) :
    ∃ current,target.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) ∧
      BeforeHeap target heap current.toNat ∧ BeforeHeap target nextHeap current.toNat := by
  obtain ⟨current,currentCell,nextBefore⟩ := second.before_heap nextSource target nextArray nextHeap nextCount stp pad scratch
  have later : nextHeap.toNat≤current.toNat := by
    obtain ⟨capacity,cell,bound⟩ := nextBefore
    omega
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,ready,built,history,length,frontier⟩ :=
    first.table_after_build source middle nextSource target array heap count maximum slices nextArray nextHeap nextCount stp pad scratch inputs entryFrame second.entryHeap second
      stateArena padArena scratchArena buffersBeforeHeap
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  have capSmall : 2^bits<2^64 := by have h:=ready.fits; change plan.table+72+57*(2^bits)+plan.padding≤33806089496 at h; omega
  have capNumber : (BitVec.ofNat 64 (2^bits)).toNat=2^bits := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt capSmall]
  refine ⟨current,currentCell,⟨BitVec.ofNat 64 (2^bits),?_,?_⟩,nextBefore⟩
  · simpa only [plan,Constructor.allocationPlan,Layout32.parameters,TableEmpty.parameters,BitVec.ofNat_toNat,BitVec.setWidth_eq] using built.header.find.capacity
  · rw [capNumber]
    change plan.table+72+57*plan.capacity+plan.padding≤current.toNat
    change plan.table+72+57*plan.capacity+plan.padding=nextHeap.toNat at frontier
    omega

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.before_after_build
