import InitECandidate.Solver.Input.PBytesProgram
import InitECandidate.Solver.Input.HeapReleaseReturn
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.PBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual normal packed hash/release restores the saved outer mark after
the real inner list hash restores its own current heap cursor. -/
theorem after_pack_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := packing_geometry cursor n small arena aligned
  have args := list_arguments source cursor out n packed count output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterList value (safe.summary_full source).2.1 run
  have nextHeap := PListChunks.ignored_return_heap source middle cursor (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out (BitVec.ofNat 64 n) stp accel chunk zeros (PackBytes.chunks n)
    chunkBound workspace heap packedArena temporaryArena temporaryAligned outArena listArguments args normal
  have summary := safe.summary_full source
  unfold LocalSummary at summary
  rw [normal] at summary
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (summary.1 rfl).trans saved
  have fields := evaluation_fields source middle _ none normal
  exact HeapScope.release_return_heap middle post mark (cursor+BitVec.ofNat 64 (PackBytes.padded n)) (fields.2.2.2.symm ▸ workspace.sha.installed) nextMark nextHeap value remaining

/-- The actual normal scoped pack invocation derives its returned tuple,
normal continuation and saved-caller restoration before applying the real
hash/release suffix. -/
theorem after_mark_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := packing_geometry cursor n small arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code workspace.sha.installed)
  obtain ⟨funded,target,returned,final,actual,checked,continued,endpoint⟩ := CallNormal.scoped_normal source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n)
    PackBytes.body afterPack callee PackBytes.returnShape args called value run
  have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n small workspace.sha.installed nLocal heap packedArena returned actual
  have calleeWorkspace := SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace
  have nextWorkspace := SszHash.Workspace.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros calleeWorkspace PackBytes.body (some (.returned returned)) actual
    (fun key different=>PackBytes.globals key source.code workspace.sha.installed different)
  let resumed := CallNormal.continuationEntry source target "pk" returned
  have resumedWorkspace := SszHash.Workspace.of_fields target resumed stp accel chunk zeros nextWorkspace rfl rfl (by intro key different; rfl)
  have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
    (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
  have currentN := (CallNormal.continuation_lookup_other source target "pk" "n" returned (by decide)).trans count
  have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
  have currentMark := (CallNormal.continuation_lookup_other source target "pk" "mark" returned (by decide)).trans saved
  have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
    change target.globals.lookup (ofString "heap_ptr")=_
    rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
  have restored := after_pack_return_heap resumed final cursor out mark stp accel chunk zeros n small resumedWorkspace pk currentN currentOut currentMark currentHeap arena aligned outArena value continued
  rw [endpoint]
  exact restored

/-- Every actual normal unchanged htr_pbytes return restores its genuine
entry heap cursor after actual packing, progressive hashing and length mix. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (small : n≤134217728) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have restored := after_mark_return_heap entry final p cursor out cursor stp accel chunk zeros n small nextWorkspace
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output) (bind_lookup_same _ _ _) heap arena aligned outArena value remaining
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.PBytes

#print axioms InitECandidate.Solver.Input.PBytes.after_pack_return_heap
#print axioms InitECandidate.Solver.Input.PBytes.after_mark_return_heap
#print axioms InitECandidate.Solver.Input.PBytes.body_return_heap
