import InitECandidate.Solver.Input.PContainerSuffixHeap

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_tmp_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (tmp+64#64))))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (tmpArena : AllocatedBytes.Arena tmp 64)
    (arena : AllocatedBytes.Arena (tmp+64#64) (832+64*n)) (cursorAligned : (tmp+64#64).toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTmp=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values ch (BitVec.ofNat 64 n) tmp) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,localVar,chunks,count,temporary,Progressive.values]
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterProgressive value (safe.summary_full source).2.1 run
  have nextHeap := Progressive.ignored_return_heap source middle ch (tmp+64#64) tmp zeros stp accel n (by omega) workspace.sha heap workspace.zerosLocal
    inputArena arena cursorAligned (AllocatedBytes.Arena.weaken tmp 64 32 tmpArena (by omega)) workspace.zeroArena progressiveArguments args normal
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize_progressive") progressiveArguments normal
  have fields := evaluation_fields source middle _ none normal
  exact after_progressive_return_heap middle post tmp mark (tmp+64#64) (fields.2.2.2.symm ▸ workspace.sha.installed)
    ((other "tmp").trans temporary) ((other "mark").trans saved) nextHeap value remaining

theorem after_mark_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have geometry := allocation_geometry tmp n arena aligned
  rw [body_shape.2.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "tmp" [.const 64#64] afterTmp tmp 64#64 rfl
    (PersistentAlloc.original_code source.code workspace.sha.installed) heap (by change tmp.toNat+64≤33806089496; have h:=arena.upper; omega) (some (.returned value)) run (by simp)
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
  have restored := after_tmp_return_heap entry final ch tmp out mark stp accel chunk zeros n short nextWorkspace
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) (bind_lookup_same _ _ _) ((other "out" (by decide)).trans output)
    ((other "mark" (by decide)).trans saved) nextHeap inputArena geometry.1 geometry.2.1 geometry.2.2.1 value remaining
  rw [endpoint]
  exact restored

/-- The real normal container call restores its entry heap, including
normal activity-mask loop and final SHA outcomes from that same execution. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (ch tmp out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n<32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)) := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post tmp "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" tmp
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name tmp different
  have restored := after_mark_return_heap entry final ch tmp out tmp stp accel chunk zeros n short nextWorkspace
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output)
    (bind_lookup_same _ _ _) heap inputArena arena aligned value remaining
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_tmp_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.after_mark_return_heap
#print axioms InitECandidate.Solver.Input.PContainer.body_return_heap
