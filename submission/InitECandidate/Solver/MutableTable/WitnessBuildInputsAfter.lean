import InitECandidate.Solver.MutableTable.WitnessBuildOutputFields

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A real preceding witness constructor retains the second constructor's
physical row cells and hash runtime. Its genuine heap advance and one
combined room inequality establish the new caller inputs, including empty
sentinels without speculative readable-array assumptions. -/
theorem Inputs.after_build (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array firstArray heap : BitVec 64) (count firstCount maximum : Nat) (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64)
    (actual : Inputs source array heap count maximum slices stp pad scratch)
    (first : Normal source target firstArray heap firstCount stp pad scratch)
    (room : heap.toNat+72+57*(4*firstCount+4)+7+72+57*(4*count+4)+7≤33806089496) :
    ∃ current,heap.toNat≤current.toNat ∧ current.toNat≤heap.toNat+72+57*(4*firstCount+4)+7 ∧
      Inputs target array current count maximum slices stp pad scratch := by
  obtain ⟨current,heapCell,heapLower,heapUpper,heapAligned,heapBound⟩ := first.heap source target firstArray heap firstCount stp pad scratch (by omega)
  obtain ⟨code,domain,endian,exceptions,oracle,globals⟩ := first.fields source target firstArray heap firstCount stp pad scratch
  have memory (index offset : Nat) (inside : index<count) (offsetInside : offset<16) :
      target.memory (byteAddress array (16*index+offset))=source.memory (byteAddress array (16*index+offset)) := by
    have positive : count≠0 := by omega
    obtain ⟨recordsLower,recordsBefore,recordsAligned⟩ := actual.records positive
    obtain ⟨stateBefore,padBefore,scratchBefore⟩ := actual.before positive
    have number:=byteAddress_toNat array (16*index+offset) (by have h:=heap.isLt; omega)
    apply first.memory
    · refine ⟨CopyGeneral.Away.before stp _ 200 array.toNat stateBefore array.isLt (by rw [number]; omega),
        CopyGeneral.Away.before pad _ 136 array.toNat padBefore array.isLt (by rw [number]; omega),
        CopyGeneral.Away.before scratch _ 32 array.toNat scratchBefore array.isLt (by rw [number]; omega)⟩
    · rw [number]
      omega
  refine ⟨current,heapLower,heapUpper,⟨?_,first.environment source target firstArray heap firstCount stp pad scratch actual.environment,
    (globals _ (by decide)).trans actual.scratchGlobal,endian.trans actual.little,heapCell,by have h:=actual.heapLower; omega,heapAligned,by omega,?_,?_,?_,
    actual.buffers,actual.before,actual.scratchAligned,actual.sizes,actual.sourceLower,
    (fun index inside=>(actual.sourceBefore index inside).trans heapLower),actual.heapAfterScratch.trans heapLower⟩⟩
  · rw [code]
    exact actual.installed
  · intro positive
    obtain ⟨lower,before,aligned⟩ := actual.records positive
    exact ⟨lower,by omega,aligned⟩
  · intro index inside
    simpa only [Nat.add_zero] using (memory index 0 inside (by decide)).trans (actual.pointers index inside)
  · intro index inside
    exact (memory index 8 inside (by decide)).trans (actual.lengths index inside)

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.after_build
