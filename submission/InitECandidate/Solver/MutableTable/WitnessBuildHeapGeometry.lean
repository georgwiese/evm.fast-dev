import InitECandidate.Solver.MutableTable.WitnessDatabaseBefore

namespace InitECandidate.Solver.MutableTable.WitnessBuild
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- A genuine constructor's exact heap/layout gives bounded, aligned,
monotone current heap geometry without assuming later allocation room. -/
theorem Normal.heap_geometry (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count : Nat) (stp pad scratch current : BitVec 64)
    (actual : Normal source target array heap count stp pad scratch)
    (cell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word current))) :
    heap.toNat≤current.toNat ∧ current.toNat≤33806089496 ∧ current.toNat%8=0 := by
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,built,history,length,ready,heapCell⟩ := actual.table
  let plan:=Constructor.allocationPlan (effectiveRecords array heap count) heap.toNat count (2^bits)
  have endBound : plan.table+72+57*plan.capacity+plan.padding≤33806089496 := ready.fits
  have word : current=BitVec.ofNat 64 (plan.table+72+57*plan.capacity+plan.padding) := by
    have equal:=cell.symm.trans heapCell
    simpa only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] using equal
  have number : current.toNat=plan.table+72+57*plan.capacity+plan.padding := by
    rw [word,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have aligned : plan.table%8=0 := ready.tableAligned
  have padded : (plan.capacity+plan.padding)%8=0 := ready.padded
  rw [number]
  change plan.table≤_ ∧ _≤_ ∧ _%8=0
  omega

/-- The real returned heap remains an ordinary aligned arena frontier. -/
theorem Normal.heap_arena (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap : BitVec 64) (count : Nat) (stp pad scratch current : BitVec 64)
    (actual : Normal source target array heap count stp pad scratch)
    (cell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word current))) :
    AllocatedBytes.Arena current 0 ∧ current.toNat%8=0 := by
  have geometry:=actual.heap_geometry source target array heap count stp pad scratch current cell
  obtain ⟨bits,stored,input,logical,lower,upper,capacity,built,history,length,ready,heapCell⟩ := actual.table
  have recordLower:=ready.recordsLower
  have before:=ready.recordsBefore
  change effectiveRecords array heap count+16*count≤heap.toNat at before
  change 2701131776≤effectiveRecords array heap count at recordLower
  exact ⟨⟨by omega,by simpa only [Nat.add_zero] using geometry.2.1⟩,geometry.2.2⟩

end InitECandidate.Solver.MutableTable.WitnessBuild

#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.heap_geometry
#print axioms InitECandidate.Solver.MutableTable.WitnessBuild.Normal.heap_arena
