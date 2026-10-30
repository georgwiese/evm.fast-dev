import InitECandidate.Solver.Mpt.CurrentStateInitMemoryContext
import InitECandidate.Solver.Input.NormalHeapEffects

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Before the block record is allocated, only the actual workspace
record and persistent frontier are required. -/
structure WorkspaceContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  heap : ∃ cursor,source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) ∧
    AllocatedBytes.Arena cursor 0 ∧ cursor.toNat≤2952790016 ∧ cursor.toNat%8=0 ∧ frontier.toNat≤cursor.toNat
  wsCell : source.globals.lookup (ofString "ws")=some (.val (.word ws))
  wsFresh : frontier.toNat≤ws.toNat ∧ ws.toNat≤2952790016
  wsArena : AllocatedBytes.Arena ws 40
  wsAligned : ws.toNat%8=0
  afterWs : NormalHeapEffects.AtLeast (ws.toNat+40) source

theorem WorkspaceContext.after_persistent {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws heap : BitVec 64}
    (context : WorkspaceContext source frontier ws) (frame : PersistentNormalFrame source target heap)
    (before : frontier.toNat≤heap.toNat)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) : WorkspaceContext target frontier ws := by
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=context.afterWs
  have sameHeap : old=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans sourceHeap)))
  subst old
  exact ⟨frame.current_arena context.arena,⟨next,cell,arena,bounded,aligned,Nat.le_trans before grows⟩,
    (frame.globals _ (by decide)).trans context.wsCell,context.wsFresh,context.wsArena,context.wsAligned,⟨next,cell,by omega,bounded,aligned⟩⟩

theorem WorkspaceContext.word_store {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws : BitVec 64}
    (context : WorkspaceContext source frontier ws) (destination expression : ExpHOL 64) (address word : BitVec 64)
    (addressRead : eval source destination=some (.val (.word address))) (wordRead : eval source expression=some (.val (.word word)))
    (fresh : frontier.toNat≤address.toNat)
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) :
    WorkspaceContext target frontier ws ∧ PersistentMemoryFrame source target frontier := by
  obtain ⟨mapped,endpoint⟩:=word_store_normal source target destination expression address word addressRead wordRead normal
  have initial : PersistentMemoryFrame source source frontier:=⟨context.heap,rfl,by intros; rfl⟩
  refine ⟨?_,initial.store_after source source target frontier destination expression address word addressRead wordRead fresh normal⟩
  rw [endpoint]
  exact ⟨⟨context.arena.scratch,context.arena.frame,context.arena.domain,context.arena.code⟩,context.heap,context.wsCell,context.wsFresh,context.wsArena,context.wsAligned,context.afterWs⟩

/-- The observed block-record allocation supplies both the genuine new bs
pointer and the heap room needed to initialize the later block-state suffix. -/
theorem WorkspaceContext.allocate_block {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws : BitVec 64}
    (context : WorkspaceContext source frontier ws)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString "bs"),none)) (ofString "alloc") [.const 80#64])=(none,target)) :
    ∃ bs,MemoryContext target frontier ws bs ∧ PersistentMemoryFrame source target frontier := by
  obtain ⟨cursor,cell,cursorArena,bounded,aligned,before⟩:=context.heap
  obtain ⟨room,funded,endpoint⟩:=PersistentAlloc.global_call_normal_any source target "bs" cursor 80#64 [.const 80#64] rfl
    (PersistentAlloc.original_code source.code context.arena.code) (Input.Trap.original_code source.code context.arena.code) cell bounded normal
  have beforeWs : ws.toNat+40≤cursor.toNat:=by
    obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=context.afterWs
    have sameHeap : old=cursor:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans cell)))
    subst old
    exact oldLower
  let allocated:=PersistentAlloc.post {source with clock:=source.clock-1} cursor 80#64
  have first : PersistentNormalFrame source allocated cursor:=
    (PersistentAlloc.post_persistent_frame {source with clock:=source.clock-1} cursor 80#64 cursorArena room).of_erase _ _ source allocated cursor rfl rfl
  have current:=context.after_persistent first before cell
  have broad:=first.memory_frame.weaken source allocated cursor frontier before
  have guards:=PersistentAlloc.guards cursor 80#64 room
  have allocatedCell : allocated.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded cursor 80#64))):=by
    simp [allocated,PersistentAlloc.post,HolFiniteMapExact.update,FUPDATE]
  have extent : NormalHeapEffects.AtLeast (cursor.toNat+80) (putGlobal allocated "bs" cursor):=
    ⟨PersistentAlloc.rounded cursor 80#64,(putGlobal.lookup_other allocated "bs" cursor _ (by decide)).trans allocatedCell,
      guards.2.2.1,guards.2.2.2.1,guards.2.2.2.2⟩
  refine ⟨cursor,?_,?_⟩
  · rw [endpoint]
    refine ⟨⟨?_,?_,current.arena.domain,current.arena.code⟩,?_,?_,putGlobal.lookup_same _ _ _,current.wsFresh,⟨before,bounded⟩,context.wsArena,context.wsAligned,⟨cursorArena.lower,by omega⟩,aligned,beforeWs,extent⟩
    · exact (putGlobal.lookup_other allocated "bs" cursor _ (by decide)).trans current.arena.scratch
    · exact (putGlobal.lookup_other allocated "bs" cursor _ (by decide)).trans current.arena.frame
    · obtain ⟨next,nextCell,nextArena,nextBound,nextAligned,grows⟩:=current.heap
      exact ⟨next,(putGlobal.lookup_other allocated "bs" cursor _ (by decide)).trans nextCell,nextArena,nextBound,nextAligned,grows⟩
    · exact (putGlobal.lookup_other allocated "bs" cursor _ (by decide)).trans current.wsCell
  · rw [endpoint]
    exact broad.put_global source allocated frontier "bs" cursor (by decide)

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.WorkspaceContext.after_persistent
#print axioms InitECandidate.Solver.Mpt.StateInit.WorkspaceContext.word_store
#print axioms InitECandidate.Solver.Mpt.StateInit.WorkspaceContext.allocate_block
