import InitECandidate.Solver.Mpt.NodeConstructorMemory
import Mathlib.Tactic.IntervalCases

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The real branch zeroing initializes every aligned field. -/
theorem branch_zero_cells (memory : WordWrites.Memory) (heap : BitVec 64) (offset : Nat)
    (inside : offset<176) (aligned : offset%8=0) :
    Zero.finalMemory memory heap 176 (heap+BitVec.ofNat 64 offset)=.word 0#64 := by
  have index : offset/8<22:=by omega
  have multiple : offset=8*(offset/8):=by omega
  generalize number : offset/8=limb at index multiple
  rw [multiple]
  interval_cases limb <;>
    simp [Zero.finalMemory,Zero.memoryWord,Zero.memory32,Copy32.memory,Copy32.writes,WordWrites.write,StoreWord.put,BitVec.add_assoc]

theorem branch_normal_cells (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (Flapjack.Basis.Pure.MlString.ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .branch)=(some (.returned value),target)) :
    ∀ offset : Nat,0<offset → offset<176 → offset%8=0 → target.memory (heap+BitVec.ofNat 64 offset)=.word 0#64 := by
  obtain ⟨answer,nodeArena,positive,frame⟩:=branch_normal source target heap domain heapCell arena aligned installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64 at memory
  intro offset nonzero inside offsetAligned
  have away : heap+BitVec.ofNat 64 offset≠heap:=by
    intro equal
    have offsets : BitVec.ofNat 64 offset=0#64:=(BitVec.add_right_inj heap).mp (equal.trans (BitVec.add_zero heap).symm)
    have number:=congrArg BitVec.toNat offsets
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at number
    change offset=0 at number
    omega
  rw [memory,StoreWord.put,if_neg away]
  exact branch_zero_cells source.memory heap offset inside offsetAligned

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_zero_cells
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_normal_cells
