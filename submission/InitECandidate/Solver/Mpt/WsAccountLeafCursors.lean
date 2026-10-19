import InitECandidate.Solver.Mpt.WsAccountLeafHeap
import InitECandidate.Solver.Rlp.ValidationArena

namespace InitECandidate.Solver.Mpt.WsAccountLeaf
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_mark_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark pointer : BitVec 64)
    (markCell : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source afterMark=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [.const 32#64]=some (PersistentAlloc.values 32#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,PersistentAlloc.values]
  obtain ⟨room,positive,inner,tailRun,restored⟩ := PersistentAlloc.call_normal source post "h" [.const 32#64] afterAlloc pointer 32#64 args
    (alloc_original_code source.code installed) (Input.Trap.original_code source.code installed) heap bounded returned normal
  let ready := bind (PersistentAlloc.post {source with clock:=source.clock-1} pointer 32#64) "h" pointer
  have currentMark : ready.locals.lookup (ofString "mark")=some (.val (.word mark)) :=
    (bind_lookup_other _ "h" "mark" pointer (by decide)).trans markCell
  have currentHeap : ready.globals.lookup (ofString "heap_ptr")=some (.val (.word (PersistentAlloc.rounded pointer 32#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded pointer 32#64)))).lookup (ofString "heap_ptr")=_
    simp [HolFiniteMapExact.update,FUPDATE]
  have value := after_alloc_heap ready inner mark (PersistentAlloc.rounded pointer 32#64) currentMark currentHeap installed returned tailRun
  rw [restored]
  exact value

/-- Complete actual normal ws_account_leaf restores the original heap mark.
Its temporary allocation's room is derived from the actual normal return. -/
theorem body_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer : BitVec 64)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
    (bounded : pointer.toNat≤33806089496) (installed : Input.OriginalCode.Installed source.code) (returned : ValueHOL 64)
    (normal : evaluateHOLFiniteState source body=(some (.returned returned),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)) := by
  rw [body_shape] at normal
  have positive := Input.CallNormal.normal_clock source post (ofString "mark") .one (ofString "heap_mark") [] afterMark returned normal
  let ready := bind {source with clock:=source.clock-1} "mark" pointer
  let inner := (evaluateHOLFiniteState ready afterMark).2
  have actual := Input.HeapScope.mark_call_execute source pointer "mark" afterMark heap (Input.HeapScope.mark_original_code source.code installed) positive
  have joined := actual.symm.trans normal
  have resultEq := congrArg Prod.fst joined
  change (evaluateHOLFiniteState ready afterMark).1=some (.returned returned) at resultEq
  have innerRun : evaluateHOLFiniteState ready afterMark=(some (.returned returned),inner) := Prod.ext resultEq rfl
  have postEq := (congrArg Prod.snd joined).symm
  change post=restore source "mark" inner at postEq
  have value := after_mark_heap ready inner pointer pointer (bind_lookup_same _ _ _) heap bounded installed returned innerRun
  rw [postEq]
  exact value

/-- The original provider's temporary work preserves its incoming RLP arena
on every outcome, with no assumed successful helper/model. -/
theorem body_arena (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor limit : BitVec 64)
    (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code)
    (result : Option (PanSemResultExact 64)) (run : evaluateHOLFiniteState source body=(result,post)) :
    Rlp.Validation.Arena post cursor limit := by
  have scratch := globals (ofString "scratch_ptr") source.code installed (by decide) source rfl
  have frame := globals (ofString "frame_mem_ptr") source.code installed (by decide) source rfl
  rw [run] at scratch frame
  have domain := (Input.evaluation_fields source post body result run).1
  exact ⟨domain.trans arena.domain,(congrArg Prod.snd scratch).trans arena.cursorGlobal,
    (congrArg Prod.snd frame).trans arena.limitGlobal,arena.ordered,arena.aligned,arena.lower,arena.upper⟩

end InitECandidate.Solver.Mpt.WsAccountLeaf

#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.after_mark_heap
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_heap
#print axioms InitECandidate.Solver.Mpt.WsAccountLeaf.body_arena
