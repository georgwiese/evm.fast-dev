import InitECandidate.Solver.Input.RequestsHashCallCost
import InitECandidate.Solver.Input.HeapReleaseReturn

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_lists_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor mark stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLists=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) containerArguments=some (PContainer.values ch 5 out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,containerArguments,localVar,ready.chunks,ready.output,PContainer.values]
  have tempArena := AllocatedBytes.Arena.weaken cursor (96*capacity+1312) (896+64*5) geometry.temporaryArena (by omega)
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "htr_pcontainer") containerArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ FixedHash.releaseSuffix value (safe.summary_full source).2.1 run
  have heap := PContainer.ignored_return_heap source middle ch cursor out stp accel chunk zeros 5 (by decide) ready.workspace ready.heap geometry.rootsArena tempArena geometry.aligned containerArguments args normal
  have nextMark := (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "htr_pcontainer") containerArguments normal).trans saved
  have fields := evaluation_fields source middle _ none normal
  exact HeapScope.release_return_heap middle post mark cursor (fields.2.2.2.symm ▸ ready.workspace.sha.installed) nextMark heap value remaining

theorem pipeline_return_heap (kinds : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor mark stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (separation : Separation rq stp accel chunk) (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (pipeline kinds)=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  induction kinds generalizing source post with
  | nil=>exact after_lists_return_heap source post rq ch out cursor mark stp accel chunk zeros pointers counts capacity ready geometry saved value run
  | cons kind rest ih=>
    change evaluateHOLFiniteState source (.seq (step kind) (pipeline rest))=(some (.returned value),post) at run
    have safe : LocalPrefix (ofString "mark") (step kind) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    have next := step_normal source middle kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry separation normal
    have nextMark := (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "htr_request_list") (arguments kind) normal).trans saved
    exact ih middle post next nextMark remaining

/-- Exact current original state after roots160 allocation. -/
theorem allocated_ready (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (image : Image source rq pointers counts)
    (arena : AllocatedBytes.Arena ch 160) (aligned : ch.toNat%8=0) : Ready (allocated source ch) rq ch out (ch+160#64) stp accel chunk zeros pointers counts := by
  let entry := allocated source ch
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by
    intro key different
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 160#64)))).lookup key=_
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different])
  have other (name : String) (different : ofString "ch"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "ch" name ch different
  have nextHeap : entry.globals.lookup (ofString "heap_ptr")=some (.val (.word (ch+160#64))) := by
    change (source.globals.update (ofString "heap_ptr",.val (.word (PersistentAlloc.rounded ch 160#64)))).lookup _=_
    rw [rounded_roots ch arena aligned]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  exact ⟨nextWorkspace,(other "rq" (by decide)).trans requests,bind_lookup_same _ _ _,(other "out" (by decide )).trans output,⟨image.fields⟩,nextHeap⟩

theorem after_mark_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out mark stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values 160#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,allocationArguments,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL]
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "ch" allocationArguments afterAllocation ch 160#64 args
    (PersistentAlloc.original_code source.code workspace.sha.installed) heap (by change ch.toNat+160≤33806089496; exact geometry.rootsArena.upper) (some (.returned value)) run (by simp)
  have ready := allocated_ready source rq ch out stp accel chunk zeros pointers counts workspace requests output image geometry.rootsArena geometry.rootsAligned
  have nextMark : (allocated source ch).locals.lookup (ofString "mark")=some (.val (.word mark)) := (bind_lookup_other _ "ch" "mark" ch (by decide)).trans saved
  have restored := pipeline_return_heap RequestListHash.kinds (allocated source ch) final rq ch out (ch+160#64) mark stp accel chunk zeros pointers counts capacity ready geometry separation nextMark value remaining
  rw [endpoint]
  exact restored

theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name ch different
  have restored := after_mark_return_heap entry final rq ch out ch stp accel chunk zeros pointers counts capacity nextWorkspace
    ((other "rq" (by decide)).trans requests) ((other "out" (by decide)).trans output) ⟨image.fields⟩ heap geometry separation (bind_lookup_same _ _ _) value remaining
  rw [endpoint]
  exact restored

/-- The real normal original caller restores its actual entry heap cursor. -/
theorem ignored_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (workspace : SszHash.Workspace source stp accel chunk zeros) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values rq out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_requests") arguments)=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)) := by
  obtain ⟨callee,called,rqLocal,outLocal⟩ := environment source.code.lookup rq out (original_code source.code workspace.sha.installed)
  obtain ⟨funded,actualValues,actualBody,actualCallee,actualShape,target,returned,actualArgs,actualCalled,bodyRun,checked,endpoint,fields⟩ := CallNormal.ignored_data source post (ofString "htr_requests") arguments run
  have valuesEq : actualValues=values rq out := Option.some.inj (actualArgs.symm.trans args)
  subst actualValues
  have entryEq : (actualBody,actualCallee,actualShape)=(body,callee,.one) := Option.some.inj (actualCalled.symm.trans called)
  cases entryEq
  have restored := body_return_heap (callEntryStateHOLFinite source callee) target rq ch out stp accel chunk zeros pointers counts capacity
    (SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace) rqLocal outLocal ⟨image.fields⟩ heap geometry separation returned bodyRun
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.after_lists_return_heap
#print axioms InitECandidate.Solver.Input.RequestsHash.pipeline_return_heap
#print axioms InitECandidate.Solver.Input.RequestsHash.allocated_ready
#print axioms InitECandidate.Solver.Input.RequestsHash.after_mark_return_heap
#print axioms InitECandidate.Solver.Input.RequestsHash.body_return_heap

#print axioms InitECandidate.Solver.Input.RequestsHash.ignored_return_heap
