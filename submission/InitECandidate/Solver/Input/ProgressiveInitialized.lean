import InitECandidate.Solver.Input.ProgressiveAllocation
import InitECandidate.Solver.Input.ProgressiveRound

namespace InitECandidate.Solver.Input.Progressive
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem initialized_locals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :
    (initialized source roots).locals=((((source.locals.update (ofString "roots",.val (.word roots))).update
      (ofString "acc",.val (.word (accPointer roots)))).update (ofString "k",.val (.word 0#64))).update
      (ofString "off",.val (.word 0#64))).update (ofString "size",.val (.word 1#64)) := rfl

theorem initialized_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (name : String)
    (a : ofString "roots"≠ofString name) (b : ofString "acc"≠ofString name) (c : ofString "k"≠ofString name)
    (d : ofString "off"≠ofString name) (e : ofString "size"≠ofString name) :
    (initialized source roots).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [initialized_locals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,a,b,c,d,e]

theorem initialized_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) :
    (initialized source roots).locals.lookup (ofString "roots")=some (.val (.word roots)) ∧
    (initialized source roots).locals.lookup (ofString "acc")=some (.val (.word (accPointer roots))) ∧
    (initialized source roots).locals.lookup (ofString "k")=some (.val (.word 0#64)) ∧
    (initialized source roots).locals.lookup (ofString "off")=some (.val (.word 0#64)) ∧
    (initialized source roots).locals.lookup (ofString "size")=some (.val (.word 1#64)) := by
  rw [initialized_locals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "size"≠ofString "roots" from by decide,show ofString "off"≠ofString "roots" from by decide,
    show ofString "k"≠ofString "roots" from by decide,show ofString "acc"≠ofString "roots" from by decide,
    show ofString "size"≠ofString "acc" from by decide,show ofString "off"≠ofString "acc" from by decide,show ofString "k"≠ofString "acc" from by decide,
    show ofString "size"≠ofString "k" from by decide,show ofString "off"≠ofString "k" from by decide,show ofString "size"≠ofString "off" from by decide]

theorem initialized_global_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64) (key : MlS) (other : key≠ofString "heap_ptr") :
    (initialized source roots).globals.lookup key=source.globals.lookup key := by
  change ((source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots 768#64)))).update
    (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (accPointer roots) 32#64)))).lookup key=_
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm other]

theorem initialized_heap (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots : BitVec 64)
    (arena : AllocatedBytes.Arena roots 800) (aligned : roots.toNat%8=0) :
    (initialized source roots).globals.lookup (ofString "heap_ptr")=some (.val (.word (temporary roots))) := by
  change ((source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded roots 768#64)))).update
    (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded (accPointer roots) 32#64)))).lookup _=_
  rw [(allocation_geometry roots arena aligned).2.2.2.2.2]
  simp [HolFiniteMapExact.lookup_update,FUPDATE]

theorem initialized_workspace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (roots stp accel : BitVec 64) (workspace : ShaPair.Workspace source stp accel) :
    ShaPair.Workspace (initialized source roots) stp accel :=
  ShaPair.Workspace.of_fields source _ stp accel workspace rfl rfl (initialized_global_other source roots _ (by decide)) (initialized_global_other source roots _ (by decide))

/-- The original roots768/acc32 allocations leave a current temporary arena
sized by actual input count; every derived pointer is physically mapped. -/
theorem initialized_geometry (roots : BitVec 64) (n : Nat) (arena : AllocatedBytes.Arena roots (832+64*n)) (aligned : roots.toNat%8=0) :
    AllocatedBytes.Arena roots 768 ∧ AllocatedBytes.Arena (accPointer roots) 32 ∧ AllocatedBytes.Arena (temporary roots) (64*n+32) ∧
      (accPointer roots).toNat%8=0 ∧ (temporary roots).toNat%8=0 := by
  have prefixArena := AllocatedBytes.Arena.weaken roots (832+64*n) 800 arena (by omega)
  have geometry := allocation_geometry roots prefixArena aligned
  have temp : temporary roots=roots+800#64 := by simp [temporary,accPointer,BitVec.add_assoc]
  refine ⟨AllocatedBytes.Arena.weaken roots _ 768 arena (by omega),AllocatedBytes.Arena.subrange roots (832+64*n) 768 32 arena (by omega),?_,geometry.2.2.1,geometry.2.2.2.1⟩
  rw [temp]
  exact AllocatedBytes.Arena.subrange roots (832+64*n) 800 (64*n+32) arena (by omega)

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.initialized_locals
#print axioms InitECandidate.Solver.Input.Progressive.initialized_other
#print axioms InitECandidate.Solver.Input.Progressive.initialized_cells
#print axioms InitECandidate.Solver.Input.Progressive.initialized_global_other
#print axioms InitECandidate.Solver.Input.Progressive.initialized_heap
#print axioms InitECandidate.Solver.Input.Progressive.initialized_workspace
#print axioms InitECandidate.Solver.Input.Progressive.initialized_geometry
