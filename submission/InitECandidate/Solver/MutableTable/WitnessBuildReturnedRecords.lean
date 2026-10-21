import InitECandidate.Solver.MutableTable.WitnessBuildOutputFields

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- Original decoded slice records survive the genuine constructor return.
The zero-count sentinel requires no mapped or readable array. -/
theorem Inputs.returned_records (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count maximum : Nat) (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64)
    (inputs : Inputs source array heap count maximum slices stp pad scratch)
    (actual : Normal source target array heap count stp pad scratch) (bits : Nat)
    (ready : AllocatedLayout.Ready (Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits))) :
    Records target (Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)) slices := by
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  by_cases zero : count=0
  · constructor <;> intro index inside <;> change index<count at inside <;> omega
  · have before:=inputs.before zero
    have kept (index offset : Nat) (inside : index<count) (offsetInside : offset<16) :
        target.memory (recordCell plan index offset)=source.memory (recordCell plan index offset) := by
      have address:=record_number plan ready index offset inside offsetInside
      have low : array.toNat≤(recordCell plan index offset).toNat := by
        rw [address]
        change array.toNat≤effectiveRecords array heap count+16*index+offset
        rw [effectiveRecords,if_neg zero]
        omega
      apply actual.memory
      · exact ⟨CopyGeneral.Away.before stp _ 200 array.toNat before.1 array.isLt low,
          CopyGeneral.Away.before pad _ 136 array.toNat before.2.1 array.isLt low,
          CopyGeneral.Away.before scratch _ 32 array.toNat before.2.2 array.isLt low⟩
      · exact record_earlier plan ready index offset inside offsetInside
    constructor
    · intro index inside
      rw [kept index 0 inside (by decide)]
      simpa [recordCell,plan,Constructor.allocationPlan,effectiveRecords,zero,byteAddress,BitVec.ofNat_add] using inputs.pointers index inside
    · intro index inside
      rw [kept index 8 inside (by decide)]
      simpa [recordCell,plan,Constructor.allocationPlan,effectiveRecords,zero,byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using inputs.lengths index inside

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.returned_records
