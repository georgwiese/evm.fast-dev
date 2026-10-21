import InitECandidate.Solver.Mpt.NodeConstructorNormal
import InitECandidate.Solver.Mpt.NodeBranchNormal

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- Branch zeroing and the final kind store preserve every word outside
the genuinely allocated node, including all earlier persistent records. -/
theorem branch_normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .branch)=(some (.returned value),target)) :
    ∀ query : BitVec 64,query.toNat<heap.toNat ∨ heap.toNat+176≤query.toNat→target.memory query=source.memory query := by
  obtain ⟨valueEq,nodeArena,funded,frame⟩:=branch_normal source target heap domain heapCell arena aligned installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64 at memory
  intro query outside
  have away : query≠heap:=by intro same; subst query; omega
  rw [memory,StoreWord.put,if_neg away]
  apply Zero.final_memory_away
  intro offset inside same
  have numeric:=congrArg BitVec.toNat same
  rw [byteAddress_toNat heap offset (by have upper:=nodeArena.upper; omega)] at numeric
  omega

/-- Every normal branch has the actual kind tag installed at its returned
address; the tag follows from the genuine write, not a tree-shape premise. -/
theorem branch_normal_tag (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (domain : source.memaddrs=InitE.ordinaryDomain)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : AllocatedBytes.Arena heap 0) (aligned : heap.toNat%8=0)
    (installed : Input.OriginalCode.Installed source.code) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (body .branch)=(some (.returned value),target)) : target.memory heap=.word 3#64 := by
  obtain ⟨valueEq,nodeArena,funded,frame⟩:=branch_normal source target heap domain heapCell arena aligned installed value normal
  have memory:=congrArg PanSemStateFiniteExact.memory frame
  change target.memory=StoreWord.put (Zero.finalMemory source.memory heap 176) heap 3#64 at memory
  rw [memory,StoreWord.put,if_pos rfl]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_normal_frame
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.branch_normal_tag
