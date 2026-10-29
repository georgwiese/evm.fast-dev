import InitECandidate.Solver.Input.PersistentNormalFrame
import InitECandidate.Solver.WitnessRadix.AllocationNormal
import InitECandidate.Solver.Input.TrapCost

namespace InitECandidate.Solver.WitnessRadix.PersistentAlloc
open Input Flapjack PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real allocator post-state has the shared frame once the observed
request room has been derived. No memory cell is initialized by allocation. -/
theorem post_persistent_frame (source : PanSemStateFiniteExact 64 Guest.HostMemory) (heap amount : BitVec 64)
    (heapArena : AllocatedBytes.Arena heap 0) (room : heap.toNat+amount.toNat≤2952790016) :
    PersistentNormalFrame source (post source heap amount) heap := by
  have checked:=guards heap amount room
  have nextArena : AllocatedBytes.Arena (rounded heap amount) 0:=
    ⟨by have lower:=heapArena.lower; have grows:=checked.2.2.1; omega,by have upper:=checked.2.2.2.1; omega⟩
  have nextCell : (post source heap amount).globals.lookup (ofString "heap_ptr")=some (.val (.word (rounded heap amount))) := by
    simp [post,HolFiniteMapExact.update,FUPDATE]
  exact ⟨⟨_,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,by have grows:=checked.2.2.1; omega⟩,rfl,
    by intro key other; simp [post,HolFiniteMapExact.update,FUPDATE,Ne.symm other],by intros; rfl⟩

/-- Actual successful allocator evaluation supplies its own room, returned
pointer and complete persistent frame. -/
theorem body_persistent_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap amount : BitVec 64)
    (amountCell : source.locals.lookup (ofString "n")=some (.val (.word amount)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned value),target)) :
    value=.val (.word heap) ∧ heap.toNat+amount.toNat≤2952790016 ∧ PersistentNormalFrame source target heap := by
  obtain ⟨valueEq,room,actual⟩:=post_of_normal source target heap amount amountCell heapCell heapBound
    (Input.Trap.original_code source.code installed) value normal
  have frame:=post_persistent_frame source heap amount heapArena room
  have physical:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>{state with clock:=0}) actual
  change LocalEffects.erase target=LocalEffects.erase (post source heap amount) at physical
  exact ⟨valueEq,room,frame.of_erase source (post source heap amount) source target heap rfl physical⟩

end InitECandidate.Solver.WitnessRadix.PersistentAlloc

#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.post_persistent_frame
#print axioms InitECandidate.Solver.WitnessRadix.PersistentAlloc.body_persistent_frame
