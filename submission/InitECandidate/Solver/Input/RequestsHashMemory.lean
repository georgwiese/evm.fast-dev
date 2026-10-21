import InitECandidate.Solver.Input.RequestsHashHeap

namespace InitECandidate.Solver.Input.RequestsHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_lists_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor stp accel chunk zeros query : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterLists=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) containerArguments=some (PContainer.values ch 5 out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,containerArguments,localVar,ready.chunks,ready.output,PContainer.values]
  have tempArena := AllocatedBytes.Arena.weaken cursor (96*capacity+1312) (896+64*5) geometry.temporaryArena (by omega)
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "htr_pcontainer") containerArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ FixedHash.releaseSuffix value (safe.summary_full source).2.1 run
  have front := PContainer.call_memory source middle ch cursor out stp accel chunk zeros query 5 (by decide) protection ready.heap geometry.rootsArena tempArena geometry.aligned below outAway containerArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have tail := HeapScope.release_return_memory middle post [localVar "mark"] query (fields.2.2.2.symm ▸ ready.workspace.sha.installed) value remaining
  exact tail.trans front

set_option maxRecDepth 4000 in
/-- Real normal request pipeline preserves arbitrary decoded/input words,
in addition to the ten metadata cells needed for its own later calls. -/
theorem pipeline_memory (kinds : List Kind) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out cursor stp accel chunk zeros query : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (ready : Ready source rq ch out cursor stp accel chunk zeros pointers counts) (geometry : Geometry rq ch cursor pointers counts capacity)
    (separation : Separation rq stp accel chunk) (protection : SszHash.Protected source stp accel chunk zeros query)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source (pipeline kinds)=(some (.returned value),post)) : post.memory query=source.memory query := by
  have cursorBelow : query.toNat<cursor.toNat := by have h:=geometry.rootsBefore; omega
  induction kinds generalizing source post with
  | nil=>exact after_lists_memory source post rq ch out cursor stp accel chunk zeros query pointers counts capacity ready geometry protection cursorBelow outAway value run
  | cons kind rest ih=>
    change evaluateHOLFiniteState source (.seq (step kind) (pipeline rest))=(some (.returned value),post) at run
    have safe : LocalPrefix (ofString "out") (step kind) := .call none _ _ (by intro name impossible; cases impossible)
    obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ _ value (safe.summary_full source).2.1 run
    obtain ⟨outArena,temporary⟩ := step_geometry rq ch cursor pointers counts capacity geometry kind
    have rootsAway := CopyGeneral.Away.after ch query 160 geometry.rootsAligned (by have h:=geometry.rootsArena.upper; omega) below
    have front := RequestListHash.call_memory source middle kind (pointers kind) cursor (ch+BitVec.ofNat 64 (32*kind.tag)) stp accel chunk zeros query (counts kind)
      (by have a:=geometry.countsBound kind; have b:=geometry.bounded; omega) protection ready.heap (geometry.inputs kind) temporary geometry.aligned outArena cursorBelow
      (CopyGeneral.Away.subrange ch query 160 (32*kind.tag) 32 rootsAway (by have h:=tag_bound kind; omega)) (arguments kind)
      (arguments_read source kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry) normal
    have next := step_normal source middle kind rq ch out cursor stp accel chunk zeros pointers counts capacity ready geometry separation normal
    have nextProtection := protection.with_workspace source middle stp accel chunk zeros query next.workspace
    exact (ih middle post next nextProtection remaining).trans front

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros query : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) allocationArguments=some (PersistentAlloc.values 160#64) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,allocationArguments,PersistentAlloc.values,valueIsWord,valueWord,panOpHOL]
  obtain ⟨paid,final,remaining,endpoint⟩ := PersistentAlloc.call_trace source post "ch" allocationArguments afterAllocation ch 160#64 args
    (PersistentAlloc.original_code source.code protection.workspace.sha.installed) heap (by change ch.toNat+160≤33806089496; exact geometry.rootsArena.upper) (some (.returned value)) run (by simp)
  have ready := allocated_ready source rq ch out stp accel chunk zeros pointers counts protection.workspace requests output image geometry.rootsArena geometry.rootsAligned
  have currentProtection := protection.with_workspace source (allocated source ch) stp accel chunk zeros query ready.workspace
  have frame := pipeline_memory RequestListHash.kinds (allocated source ch) final rq ch out (ch+160#64) stp accel chunk zeros query pointers counts capacity ready geometry separation currentProtection below outAway value remaining
  rw [endpoint]
  exact frame

/-- Whole original requests202 memory frame includes the two actual heap
scopes, all five kind calls and final five-field container hash. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros query : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (requests : source.locals.lookup (ofString "rq")=some (.val (.word rq)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post ch "mark" afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" ch
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) := bind_lookup_other _ "mark" name ch different
  have frame := after_mark_memory entry final rq ch out stp accel chunk zeros query pointers counts capacity nextProtection
    ((other "rq" (by decide)).trans requests) ((other "out" (by decide)).trans output) ⟨image.fields⟩ heap geometry separation below outAway value remaining
  rw [endpoint]
  exact frame

theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (rq ch out stp accel chunk zeros query : BitVec 64) (pointers : Kind→BitVec 64) (counts : Kind→Nat) (capacity : Nat)
    (protection : SszHash.Protected source stp accel chunk zeros query) (image : Image source rq pointers counts)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word ch)))
    (geometry : Geometry rq ch (ch+160#64) pointers counts capacity) (separation : Separation rq stp accel chunk)
    (below : query.toNat<ch.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values rq out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_requests") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,rqLocal,outLocal⟩ := environment source.code.lookup rq out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_requests") arguments (values rq out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target rq ch out stp accel chunk zeros query pointers counts capacity
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) rqLocal outLocal ⟨image.fields⟩ heap geometry separation below outAway value evaluated) run

/-- Every nonheap global is retained on all original request-hash outcomes. -/
theorem globals (key : MlS) (code) (installed : OriginalCode.Installed code) (different : key≠ofString "heap_ptr") : GlobalEffects.Preserves key code body := by
  rw [body_shape]
  unfold afterMark
  apply GlobalEffects.scoped_body key code _ _ (ofString "heap_mark") _ _ _ _ _ (HeapScope.mark_original_code code installed) (Merkle.mark_globals key code)
  apply GlobalEffects.scoped_body key code _ _ (ofString "alloc") _ _ _ _ _ (PersistentAlloc.original_code code installed) (PersistentAlloc.globals key code installed different)
  exact pipeline_globals RequestListHash.kinds key code installed different

end InitECandidate.Solver.Input.RequestsHash

#print axioms InitECandidate.Solver.Input.RequestsHash.after_lists_memory
#print axioms InitECandidate.Solver.Input.RequestsHash.pipeline_memory
#print axioms InitECandidate.Solver.Input.RequestsHash.after_mark_memory
#print axioms InitECandidate.Solver.Input.RequestsHash.body_memory
#print axioms InitECandidate.Solver.Input.RequestsHash.call_memory
#print axioms InitECandidate.Solver.Input.RequestsHash.globals
