import InitECandidate.Solver.Input.PContainerSuffixMemory
import InitECandidate.Solver.Input.PContainerCallCost
import InitECandidate.Solver.Input.ProgressiveMemory

namespace InitECandidate.Solver.Input.PContainer
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original progressive tree and activity-mask suffix preserve protected
words below their real temporary64 allocation and outside caller output. -/
theorem after_tmp_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ch tmp out stp accel chunk zeros query : BitVec 64) (n : Nat) (short : n<32)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (temporary : source.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (tmp+64#64))))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (below : query.toNat<tmp.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterTmp=(some (.returned value),post)) : post.memory query=source.memory query := by
  have geometry := allocation_geometry tmp n arena aligned
  have number : (tmp+64#64).toNat=tmp.toNat+64 := BitVec.toNat_add_of_lt (by change tmp.toNat+64<2^64; have h:=arena.upper; omega)
  have tmpAway := CopyGeneral.Away.after tmp query 64 aligned (by have h:=arena.upper; omega) below
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) progressiveArguments=some (Progressive.values ch (BitVec.ofNat 64 n) tmp) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,progressiveArguments,localVar,chunks,count,temporary,Progressive.values]
  rw [body_shape.2.2.1] at run
  have safe : LocalPrefix (ofString "tmp") (.call (some (none,none)) (ofString "merkleize_progressive") progressiveArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ afterProgressive value (safe.summary_full source).2.1 run
  have front := Progressive.call_memory source middle ch (tmp+64#64) tmp zeros stp accel chunk query n (by omega) protection heap inputArena geometry.2.1 geometry.2.2.1
    (AllocatedBytes.Arena.weaken tmp (896+64*n) 32 arena (by omega)) (by rw [number]; omega) (by intro offset inside; exact tmpAway offset (by omega)) progressiveArguments args normal
  have nextWorkspace := SszHash.Workspace.after source middle stp accel chunk zeros protection.workspace _ none normal
    (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "merkleize_progressive") progressiveArguments Progressive.formals Progressive.body .one
      (Progressive.original_code source.code protection.workspace.sha.installed) (Progressive.globals key source.code protection.workspace.sha.installed different))
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize_progressive") progressiveArguments normal
  exact (after_progressive_memory middle post tmp out stp accel query n short nextWorkspace.sha ((other "tmp").trans temporary) ((other "out").trans output) ((other "n").trans count)
    geometry.1 aligned tmpAway protection.stateAway protection.accelAway outAway value remaining).trans front

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ch tmp out stp accel chunk zeros query : BitVec 64) (n : Nat) (short : n<32)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (below : query.toNat<tmp.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have geometry := allocation_geometry tmp n arena aligned
  rw [body_shape.2.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "tmp" [.const 64#64] afterTmp tmp 64#64 rfl
    (PersistentAlloc.original_code source.code protection.workspace.sha.installed) heap (by change tmp.toNat+64≤33806089496; have h:=arena.upper; omega) (some (.returned value)) run (by simp)
  let entry := bind (PersistentAlloc.post {source with clock:=source.clock-1} tmp 64#64) "tmp" tmp
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded tmp 64#64)))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have other (name : String) (different : ofString "tmp"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "tmp" name tmp different
  have nextHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (tmp+64#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded tmp 64#64)))).lookup _=_
    rw [geometry.2.2.2]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have frame := after_tmp_memory entry final ch tmp out stp accel chunk zeros query n short nextProtection
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) (bind_lookup_same _ _ _) ((other "out" (by decide)).trans output)
    nextHeap inputArena arena aligned below outAway value remaining
  rw [endpoint]
  exact frame

/-- Complete unchanged container body preserves decoded memory through its
actual allocations, progressive tree, activity bits, SHA pair and release. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ch tmp out stp accel chunk zeros query : BitVec 64) (n : Nat) (short : n<32)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (chunks : source.locals.lookup (ofString "ch")=some (.val (.word ch)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (below : query.toNat<tmp.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post tmp "mark" afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" tmp
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name tmp different
  have frame := after_mark_memory entry final ch tmp out stp accel chunk zeros query n short nextProtection
    ((other "ch" (by decide)).trans chunks) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output) heap inputArena arena aligned below outAway value remaining
  rw [endpoint]
  exact frame

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (ch tmp out stp accel chunk zeros query : BitVec 64) (n : Nat) (short : n<32)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word tmp)))
    (inputArena : AllocatedBytes.Arena ch (32*n)) (arena : AllocatedBytes.Arena tmp (896+64*n)) (aligned : tmp.toNat%8=0)
    (below : query.toNat<tmp.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values ch n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pcontainer") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,chLocal,nLocal,outLocal⟩ := environment source.code.lookup ch n out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_pcontainer") arguments (values ch n out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target ch tmp out stp accel chunk zeros query n short
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) chLocal nLocal outLocal heap inputArena arena aligned below outAway value evaluated) run

end InitECandidate.Solver.Input.PContainer

#print axioms InitECandidate.Solver.Input.PContainer.after_tmp_memory
#print axioms InitECandidate.Solver.Input.PContainer.after_mark_memory
#print axioms InitECandidate.Solver.Input.PContainer.body_memory
#print axioms InitECandidate.Solver.Input.PContainer.call_memory
