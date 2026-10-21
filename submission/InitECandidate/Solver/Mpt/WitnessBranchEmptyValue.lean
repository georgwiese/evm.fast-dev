import InitECandidate.Solver.Mpt.WitnessBranchValueView
import InitECandidate.Solver.Mpt.WitnessDecodeBranchNormal
import InitECandidate.Solver.Mpt.WitnessRecordMemory

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The final two actual word-zero stores initialize the branch value
words, independently of all prior memory contents. -/
theorem branch_allocated_empty (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) :
    WitnessCore.EmptyValue (branchAllocated source heap) heap := by
  have away : heap+160#64≠heap+168#64 := by
    intro equal
    exact (by decide : (160#64 : BitVec 64)≠168#64) ((BitVec.add_right_inj heap).mp equal)
  have away160 : heap+160#64≠heap := by
    intro equal
    have zero : (160#64 : BitVec 64)=0#64 := (BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using equal)
    cases zero
  have away168 : heap+168#64≠heap := by
    intro equal
    have zero : (168#64 : BitVec 64)=0#64 := (BitVec.add_right_inj heap).mp (by simpa only [BitVec.add_zero] using equal)
    cases zero
  constructor
  · change StoreWord.put (StoreWord.put (StoreWord.put (Zero.memory32 source.memory heap 0 5) (heap+160#64) 0#64) (heap+168#64) 0#64) heap 3#64 (heap+160#64)=.word 0#64
    simp [StoreWord.put,away160,away]
  · change StoreWord.put (StoreWord.put (StoreWord.put (Zero.memory32 source.memory heap 0 5) (heap+160#64) 0#64) (heap+168#64) 0#64) heap 3#64 (heap+168#64)=.word 0#64
    simp [StoreWord.put,away168]

/-- The real branch decoder's scratch-record stores retain those zero
value words in its genuine returned physical state. -/
theorem branch_empty_normal (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer length count heap cursor limit : BitVec 64)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word length)))
    (sliceCell : source.locals.lookup (ofString "sl")=some (Rlp.Slices.result array count))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapAligned : heap.toNat%8=0)
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤heap.toNat)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source branchBody=(some (.returned value),target)) : WitnessCore.EmptyValue target heap := by
  obtain ⟨countEq,nodeArena,room,recordArena,nextArena,decreases,valueEq,funded,post⟩ := branch_normal source target array pointer length count heap cursor limit
    arrayCell pointerCell lengthCell sliceCell heapCell heapArena heapAligned arena installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory post
  change target.memory=WordWrites.write (branchAllocated source heap).memory
    (LocalFields.writes (WitnessRecord.pointer cursor) (branchFields (branchWords array pointer length heap))) at memory
  apply (branch_allocated_empty source heap).frame (branchAllocated source heap) target heap
  all_goals
    rw [memory]
    apply WitnessRecord.writes_above source cursor limit arena room _
      (by intro field member; have geometry:=branch_geometry (branchWords array pointer length heap) field member; omega)
    have upper:=nodeArena.upper
    have number160 : (heap+160#64).toNat=heap.toNat+160 := byteAddress_toNat heap 160 (by omega)
    have number168 : (heap+168#64).toNat=heap.toNat+168 := byteAddress_toNat heap 168 (by omega)
    omega

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_allocated_empty
#print axioms InitECandidate.Solver.Mpt.WitnessDecode.branch_empty_normal
