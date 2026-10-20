import InitECandidate.Solver.Input.PContainerAllocatedCost
import InitECandidate.Solver.Input.AllocationTrace
import InitECandidate.Solver.Input.HeapMarkTrace

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem allocation_geometry (tmp : BitVec 64) (n : Nat) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0) :
    AllocatedBytes.Arena tmp 64 ∧ AllocatedBytes.Arena (tmp+64#64) (832+64*n) ∧
    (tmp+64#64).toNat%8=0 ∧ PersistentAlloc.rounded tmp 64#64=tmp+64#64 := by
  have upper := arena.upper
  have number : (tmp+64#64).toNat=tmp.toNat+64 := BitVec.toNat_add_of_lt (by change tmp.toNat+64<2^64; omega)
  refine ⟨AllocatedBytes.Arena.weaken tmp _ 64 arena (by omega),AllocatedBytes.Arena.subrange tmp (896+64*n) 64 (832+64*n) arena (by omega),by rw [number]; omega,?_⟩
  apply BitVec.eq_of_toNat_eq
  rw [PersistentAlloc.rounded_nat tmp 64#64 (by change tmp.toNat+64+7<2^64; omega),number]
  change (tmp.toNat+64+7)/8*8=tmp.toNat+64
  omega

theorem after_mark_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source afterMark=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤116*n+24204 := by
  have geometry := allocation_geometry tmp n arena aligned
  rw [body_shape.2.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "tmp" [.const 64#64] afterTmp tmp 64#64 rfl
    (PersistentAlloc.original_code source.code workspace.sha.installed) heap (by change tmp.toNat+64≤33806089496; have h:=arena.upper; omega) result run notTimeout
  let entry := bind (PersistentAlloc.post {source with clock:=source.clock-1} tmp 64#64) "tmp" tmp
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded tmp 64#64)))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have other (name : String) (different : ofString "tmp"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "tmp" name tmp different
  have nextHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (tmp+64#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded tmp 64#64)))).lookup _=_
    rw [geometry.2.2.2]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have price := after_tmp_cost entry final ch tmp out stp accel chunk zeros n short nextWorkspace
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) (bind_lookup_same _ _ _) ((other "out" (by decide)).trans output)
    nextHeap inputArena geometry.1 geometry.2.1 aligned geometry.2.2.1 result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry afterTmp
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

/-- Whole unchanged container hashing at the actual small field count.
Includes mark/allocation, progressive root, activity bits, pair and release. -/
theorem body_cost (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) (notTimeout : result≠some .timeOut) :
    source.clock-post.clock≤116*n+24205 := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post tmp "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) result run notTimeout
  let entry := bind {source with clock:=source.clock-1} "mark" tmp
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name tmp different
  have price := after_mark_cost entry final ch tmp out stp accel chunk zeros n short nextWorkspace
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output)
    heap inputArena arena aligned result remaining notTimeout
  have monotone := evaluateHOLFiniteState_clock_le entry afterMark
  rw [remaining] at monotone
  change final.clock≤entry.clock at monotone
  have entryClock : entry.clock=source.clock-1 := rfl
  have endpointClock : post.clock=final.clock := by rw [endpoint]; rfl
  rw [endpointClock]
  omega

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.allocation_geometry
#print axioms InitECandidate.Solver.Input.PContainer.after_mark_cost
#print axioms InitECandidate.Solver.Input.PContainer.body_cost
