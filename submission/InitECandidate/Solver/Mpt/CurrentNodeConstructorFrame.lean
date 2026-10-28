import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Input.PersistentNormalFrame

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The current scalar constructor's own normal allocation derives its
request room, bounded aligned next frontier and complete earlier-word frame. -/
theorem scalar_persistent_frame (kind : Kind) (scalar : kind≠.branch)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (inputs : Inputs kind source words) (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (installed : OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body kind)=(some (.returned value),target)) :
    value=.val (.word heap) ∧ PersistentNormalFrame source target heap := by
  obtain ⟨valueEq,room,nodeArena,funded,exactFrame⟩:=scalar_normal kind scalar source target heap words inputs domain heapCell heapArena heapBound aligned installed value normal
  have amountNumber : (BitVec.ofNat 64 (bytes kind)).toNat=bytes kind:=by cases kind <;> rfl
  have checked:=PersistentAlloc.guards heap (BitVec.ofNat 64 (bytes kind)) (by rw [amountNumber]; exact room)
  have globals:=congrArg PanSemStateFiniteExact.globals exactFrame
  change target.globals=(PersistentAlloc.post source heap (BitVec.ofNat 64 (bytes kind))).globals at globals
  have nextCell : target.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))))) := by
    rw [globals]
    simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have nextArena : AllocatedBytes.Arena (PersistentAlloc.rounded heap (BitVec.ofNat 64 (bytes kind))) 0:=
    ⟨by have lower:=heapArena.lower; have grows:=checked.2.2.1; omega,by have upper:=checked.2.2.2.1; omega⟩
  have metadata:=congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory=>MemoryMetadata.erase {state with globals:=source.globals}) exactFrame
  change MemoryMetadata.erase {target with globals:=source.globals}=MemoryMetadata.erase source at metadata
  exact ⟨valueEq,⟨⟨_,nextCell,nextArena,checked.2.2.2.1,checked.2.2.2.2,by have grows:=checked.2.2.1; omega⟩,metadata,
    by intro key other; rw [globals]; simp [PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE,Ne.symm other],
    fun query before=>scalar_normal_frame kind scalar source target heap words inputs domain heapCell heapArena heapBound aligned installed value normal query (Or.inl before)⟩⟩

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.scalar_persistent_frame
