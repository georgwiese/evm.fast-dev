import InitECandidate.Solver.Input.PersistentMemoryFrame
import InitECandidate.Solver.Input.NormalHeapEffects
import InitECandidate.Solver.Input.PersistentAllocationFrame
import InitECandidate.Solver.Input.CurrentTable.NewScalarCall
import InitECandidate.Solver.WitnessRadix.AllocationGlobalNormal

namespace InitECandidate.Solver.Mpt.StateInit
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual block-state suffix needs only its two fresh global records
and a current bounded heap. Earlier input contents are protected by the
separate normal frame rather than included as future success assumptions. -/
structure MemoryContext (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frontier ws bs : BitVec 64) : Prop where
  arena : CurrentStartup.ArenaState source
  heap : ∃ cursor,source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) ∧
    AllocatedBytes.Arena cursor 0 ∧ cursor.toNat≤2952790016 ∧ cursor.toNat%8=0 ∧ frontier.toNat≤cursor.toNat
  wsCell : source.globals.lookup (ofString "ws")=some (.val (.word ws))
  bsCell : source.globals.lookup (ofString "bs")=some (.val (.word bs))
  wsFresh : frontier.toNat≤ws.toNat ∧ ws.toNat≤2952790016
  bsFresh : frontier.toNat≤bs.toNat ∧ bs.toNat≤2952790016
  wsArena : AllocatedBytes.Arena ws 40
  wsAligned : ws.toNat%8=0
  bsArena : AllocatedBytes.Arena bs 80
  bsAligned : bs.toNat%8=0
  wsBeforeBs : ws.toNat+40≤bs.toNat
  afterBs : NormalHeapEffects.AtLeast (bs.toNat+80) source

theorem MemoryContext.after_persistent {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs heap : BitVec 64}
    (context : MemoryContext source frontier ws bs) (frame : PersistentNormalFrame source target heap)
    (before : frontier.toNat≤heap.toNat)
    (sourceHeap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))) : MemoryContext target frontier ws bs := by
  obtain ⟨next,cell,arena,bounded,aligned,grows⟩:=frame.nextHeap
  obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=context.afterBs
  have sameHeap : old=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (oldCell.symm.trans sourceHeap)))
  subst old
  exact ⟨frame.current_arena context.arena,⟨next,cell,arena,bounded,aligned,Nat.le_trans before grows⟩,
    (frame.globals _ (by decide)).trans context.wsCell,(frame.globals _ (by decide)).trans context.bsCell,context.wsFresh,context.bsFresh,context.wsArena,context.wsAligned,context.bsArena,context.bsAligned,context.wsBeforeBs,⟨next,cell,by omega,bounded,aligned⟩⟩

theorem MemoryContext.put_global {source : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (context : MemoryContext source frontier ws bs) (name : String) (word : BitVec 64)
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name) :
    MemoryContext (putGlobal source name word) frontier ws bs := by
  obtain ⟨cursor,cell,arena,bounded,aligned,grows⟩:=context.heap
  have extent : NormalHeapEffects.AtLeast (bs.toNat+80) (putGlobal source name word):=by
    obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=context.afterBs
    exact ⟨old,(putGlobal.lookup_other source name word _ notHeap).trans oldCell,oldLower,oldBound,oldAligned⟩
  refine ⟨⟨?_,?_,context.arena.domain,context.arena.code⟩,
    ⟨cursor,(putGlobal.lookup_other source name word _ notHeap).trans cell,arena,bounded,aligned,grows⟩,
    (putGlobal.lookup_other source name word _ notWs).trans context.wsCell,
    (putGlobal.lookup_other source name word _ notBs).trans context.bsCell,context.wsFresh,context.bsFresh,context.wsArena,context.wsAligned,context.bsArena,context.bsAligned,context.wsBeforeBs,extent⟩
  · exact (putGlobal.lookup_other source name word _ notScratch).trans context.arena.scratch
  · exact (putGlobal.lookup_other source name word _ notFrame).trans context.arena.frame

theorem MemoryContext.word_store {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (context : MemoryContext source frontier ws bs) (destination expression : ExpHOL 64) (address word : BitVec 64)
    (addressRead : eval source destination=some (.val (.word address))) (wordRead : eval source expression=some (.val (.word word)))
    (fresh : frontier.toNat≤address.toNat)
    (normal : evaluateHOLFiniteState source (.store destination expression)=(none,target)) :
    MemoryContext target frontier ws bs ∧ PersistentMemoryFrame source target frontier := by
  obtain ⟨mapped,endpoint⟩:=word_store_normal source target destination expression address word addressRead wordRead normal
  have initial : PersistentMemoryFrame source source frontier:=⟨context.heap,rfl,by intros; rfl⟩
  refine ⟨?_,initial.store_after source source target frontier destination expression address word addressRead wordRead fresh normal⟩
  rw [endpoint]
  exact ⟨⟨context.arena.scratch,context.arena.frame,context.arena.domain,context.arena.code⟩,
    context.heap,context.wsCell,context.bsCell,context.wsFresh,context.bsFresh,context.wsArena,context.wsAligned,context.bsArena,context.bsAligned,context.wsBeforeBs,context.afterBs⟩

/-- Global initialization allocations derive their exact advancing state
from the actual normally continuing call. Existing ws/bs remain intact. -/
theorem MemoryContext.allocate_global {source post : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (context : MemoryContext source frontier ws bs) (name : String) (amount : BitVec 64) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (PersistentAlloc.values amount))
    (notHeap : ofString "heap_ptr"≠ofString name) (notWs : ofString "ws"≠ofString name) (notBs : ofString "bs"≠ofString name)
    (notScratch : ofString "scratch_ptr"≠ofString name) (notFrame : ofString "frame_mem_ptr"≠ofString name)
    (normal : evaluateHOLFiniteState source (.call (some (some (.global,ofString name),none)) (ofString "alloc") arguments)=(none,post)) :
    MemoryContext post frontier ws bs ∧ PersistentMemoryFrame source post frontier := by
  obtain ⟨cursor,cell,cursorArena,bounded,aligned,before⟩:=context.heap
  obtain ⟨room,funded,endpoint⟩:=PersistentAlloc.global_call_normal_any source post name cursor amount arguments args
    (PersistentAlloc.original_code source.code context.arena.code) (Input.Trap.original_code source.code context.arena.code) cell bounded normal
  let allocated:=PersistentAlloc.post {source with clock:=source.clock-1} cursor amount
  have first : PersistentNormalFrame source allocated cursor:=
    (PersistentAlloc.post_persistent_frame {source with clock:=source.clock-1} cursor amount cursorArena room).of_erase _ _ source allocated cursor rfl rfl
  have current:=(context.after_persistent first before cell).put_global name cursor notHeap notWs notBs notScratch notFrame
  have broad : PersistentMemoryFrame source allocated frontier:=
    ⟨by obtain ⟨next,heapCell,arena,upper,alignment,grows⟩:=first.nextHeap; exact ⟨next,heapCell,arena,upper,alignment,Nat.le_trans before grows⟩,
      first.metadata,fun query earlier=>first.memory query (by omega)⟩
  rw [endpoint]
  exact ⟨current,broad.put_global source allocated frontier name cursor notHeap⟩

/-- These actual allocated records and typed globals are independent of
callee local bindings and clock. -/
theorem MemoryContext.of_frame {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (context : MemoryContext source frontier ws bs) (same : LocalEffects.erase target=LocalEffects.erase source) :
    MemoryContext target frontier ws bs := by
  have globals:=congrArg PanSemStateFiniteExact.globals same
  change target.globals=source.globals at globals
  obtain ⟨heap,cell,owned,bounded,aligned,advanced⟩:=context.heap
  have extent : NormalHeapEffects.AtLeast (bs.toNat+80) target:=by
    obtain ⟨old,oldCell,oldLower,oldBound,oldAligned⟩:=context.afterBs
    exact ⟨old,by rw [globals]; exact oldCell,oldLower,oldBound,oldAligned⟩
  exact ⟨context.arena.of_frame same,⟨heap,by rw [globals]; exact cell,owned,bounded,aligned,advanced⟩,
    by rw [globals]; exact context.wsCell,by rw [globals]; exact context.bsCell,context.wsFresh,context.bsFresh,
    context.wsArena,context.wsAligned,context.bsArena,context.bsAligned,context.wsBeforeBs,extent⟩

/-- Actual later metadata/global/heap facts retain these same owned
records even when a helper writes to its own workspaces. Record contents
are transported separately by the helper's actual memory frame. -/
theorem MemoryContext.of_fields {source target : PanSemStateFiniteExact 64 Guest.HostMemory} {frontier ws bs : BitVec 64}
    (context : MemoryContext source frontier ws bs) (arena : CurrentStartup.ArenaState target)
    (extent : NormalHeapEffects.AtLeast (bs.toNat+80) target)
    (wsCell : target.globals.lookup (ofString "ws")=some (.val (.word ws)))
    (bsCell : target.globals.lookup (ofString "bs")=some (.val (.word bs))) :
    MemoryContext target frontier ws bs := by
  obtain ⟨heap,cell,lower,bounded,aligned⟩:=extent
  have owned : AllocatedBytes.Arena heap 0:=⟨by have low:=context.bsArena.lower; omega,by omega⟩
  exact ⟨arena,⟨heap,cell,owned,bounded,aligned,by have before:=context.bsFresh.1; omega⟩,wsCell,bsCell,
    context.wsFresh,context.bsFresh,context.wsArena,context.wsAligned,context.bsArena,context.bsAligned,
    context.wsBeforeBs,heap,cell,lower,bounded,aligned⟩

end InitECandidate.Solver.Mpt.StateInit

#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.after_persistent
#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.put_global
#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.word_store
#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.allocate_global

#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.of_frame
#print axioms InitECandidate.Solver.Mpt.StateInit.MemoryContext.of_fields
