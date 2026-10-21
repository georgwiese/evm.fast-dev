import InitECandidate.Solver.WitnessRadix.AllocationCost
import InitECandidate.Solver.MutableTable.WitnessBuildOriginalHelpers

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Current caller-side physical constructor data. The empty branch places
no mapping or arena requirement on its original array sentinel. -/
structure Inputs (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64) : Prop where
  installed : Input.OriginalCode.Installed source.code
  environment : Keccak256.Environment source stp pad
  scratchGlobal : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word scratch))
  little : source.be=false
  heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
  heapLower : 2701131776≤heap.toNat
  heapAligned : heap.toNat%8=0
  room : heap.toNat+72+57*(4*count+4)+7≤33806089496
  records : count≠0 → 2701131776≤array.toNat ∧ array.toNat+16*count≤heap.toNat ∧ array.toNat%8=0
  pointers : ∀ index<count,source.memory (byteAddress array (16*index))=.word (slices index).1
  lengths : ∀ index<count,source.memory (byteAddress array (16*index+8))=.word (slices index).2
  buffers : ∀ index<count,Keccak256.Buffers stp (slices index).1 pad scratch (slices index).2.toNat
  before : count≠0 → stp.toNat+200≤array.toNat ∧ pad.toNat+136≤array.toNat ∧ scratch.toNat+32≤array.toNat
  scratchAligned : scratch.toNat%8=0
  sizes : ∀ index<count,(slices index).2.toNat≤maximum
  sourceLower : ∀ index<count,2713731432≤(slices index).1.toNat
  sourceBefore : ∀ index<count,(slices index).1.toNat+(slices index).2.toNat≤heap.toNat
  heapAfterScratch : scratch.toNat+32≤heap.toNat

/-- Normal argument lookup supplies only the two real local bindings;
all remaining callee preconditions follow from current caller data. -/
theorem Inputs.callee (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array heap : BitVec 64) (count maximum : Nat)
    (slices : Nat→Graph.Slice) (stp pad scratch : BitVec 64)
    (actual : Inputs source array heap count maximum slices stp pad scratch)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (arrayCell : callee.lookup (ofString "slice_arr")=some (.val (.word array)))
    (countCell : callee.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 count)))) :
    (count=0 ∧ EmptyReady (callEntryStateHOLFinite source callee) heap.toNat) ∨
      count≠0 ∧ Ready (callEntryStateHOLFinite source callee) array.toNat heap.toNat count maximum slices stp pad scratch := by
  let entry:=callEntryStateHOLFinite source callee
  have helpers:=original_helpers source.code actual.installed
  have heapCell : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (BitVec.ofNat 64 heap.toNat))) := by
    change source.globals.lookup (ofString "heap_ptr")=_
    simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using actual.heapGlobal
  by_cases empty : count=0
  · refine Or.inl ⟨empty,actual.heapLower,actual.heapAligned,?_,actual.environment.domain,actual.little,?_,heapCell,helpers.tableCode,
      PersistentAlloc.original_code source.code actual.installed,actual.environment.zeroCode⟩
    · have room:=actual.room
      rw [empty] at room
      omega
    · change callee.lookup (ofString "n")=_
      simpa only [empty] using countCell
  · obtain ⟨recordsLower,recordsBefore,recordsAligned⟩ := actual.records empty
    have environment:=Keccak256.Environment.of_fields source entry stp pad actual.environment rfl rfl rfl (by intro key other; rfl)
    refine Or.inr ⟨empty,recordsLower,recordsBefore,recordsAligned,actual.heapAligned,actual.room,?_,countCell,heapCell,helpers.tableCode,
      PersistentAlloc.original_code source.code actual.installed,?_,?_⟩
    · change callee.lookup (ofString "slice_arr")=_
      simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using arrayCell
    · constructor
      · intro index inside
        change source.memory _=_
        simpa [recordCell,Constructor.allocationPlan,byteAddress,BitVec.ofNat_add] using actual.pointers index inside
      · intro index inside
        change source.memory _=_
        simpa [recordCell,Constructor.allocationPlan,byteAddress,BitVec.ofNat_add,BitVec.add_assoc] using actual.lengths index inside
    · exact ⟨actual.scratchGlobal,Keccak256.original_code source.code actual.installed,environment,actual.buffers,actual.before empty,actual.scratchAligned,actual.little,
        helpers.hashCode,by change source.code.lookup (ofString "memcpy")=_; exact actual.environment.copyCode,helpers.insertCode,helpers.compareCode,helpers.findCode,helpers.setCode,actual.sizes⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Inputs.callee
