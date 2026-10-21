import InitECandidate.Solver.Input.BytesListProgram
import InitECandidate.Solver.Input.HeapReleaseNormal
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopedCallNormal
import InitECandidate.Solver.Input.IgnoredCallLookup
import InitECandidate.Solver.Input.SequenceReturned

namespace InitECandidate.Solver.Input.BytesListHash
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

theorem after_merkle_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (mark old : BitVec 64)
    (installed : OriginalCode.Installed source.code)
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word old)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMerkle=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.2.1] at run
  obtain ⟨released,normal,remaining⟩ := sequence_returned source post _ afterRelease value (safe.summary_full source).2.1 run
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "mark"]=some [.val (.word mark)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,localVar,saved]
  have releasedEq := HeapScope.release_normal source released mark old [localVar "mark"] args heap installed normal
  have releasedHeap : released.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
    rw [releasedEq]
    simp [HeapScope.releasePost,HolFiniteMapExact.lookup_update,FUPDATE]
  have fields := evaluation_fields source released _ none normal
  have code : OriginalCode.Installed released.code := fields.2.2.2.symm ▸ installed
  have pure : GlobalEffects.Preserves (ofString "heap_ptr") released.code afterRelease := by
    rw [body_shape.2.2.2.2]
    exact GlobalEffects.sequence (ofString "heap_ptr") released.code _ _
      (GlobalEffects.call_body (ofString "heap_ptr") released.code (some none) (ofString "mix_in_length") mixArguments MixLength.formals MixLength.body .one
        (MixLength.original_code released.code code) (MixLength.globals (ofString "heap_ptr") released.code code)) (GlobalEffects.returned (ofString "heap_ptr") released.code _)
  have frame := pure released rfl
  rw [remaining] at frame
  exact (congrArg Prod.snd frame).trans releasedHeap

theorem after_pack_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have chunksBound := extra_chunks n short
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have merkleArena := AllocatedBytes.Arena.weaken _ (832+64*PackBytes.chunks n) (32*max 1 (2*PackBytes.chunks n)) temporaryArena (by omega)
  have args := merkle_arguments source cursor out n packed limitLocal output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterMerkle value (safe.summary_full source).2.1 run
  have nextHeap := Merkle.ignored_return_heap source middle cursor (BitVec.ofNat 64 (PackBytes.chunks n)) 1#64 (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out stp accel 0 (by decide)
    (by rw [number]; change PackBytes.chunks n≤1; exact chunksBound) (by decide) workspace.sha heap
    (by rw [number]; exact packedArena) (by rw [number]; exact merkleArena) temporaryAligned merkleArguments args normal
  have nextMark : middle.locals.lookup (ofString "mark")=some (.val (.word mark)) := (CallNormal.ignored_lookup source middle (ofString "mark") (ofString "merkleize") merkleArguments normal).trans saved
  have fields := evaluation_fields source middle _ none normal
  exact after_merkle_return_heap middle post mark (cursor+BitVec.ofNat 64 (PackBytes.padded n)) (fields.2.2.2.symm ▸ workspace.sha.installed) nextMark nextHeap value remaining

theorem after_mark_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out mark stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (saved : source.locals.lookup (ofString "mark")=some (.val (.word mark)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word mark)) := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code workspace.sha.installed)
  rw [body_shape.2.1] at run
  obtain ⟨funded,target,returned,final,actual,checked,continued,endpoint⟩ := CallNormal.scoped_normal source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n)
    PackBytes.body afterPack callee PackBytes.returnShape args called value run
  have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n (by omega) workspace.sha.installed nLocal heap packedArena returned actual
  have calleeWorkspace := SszHash.Workspace.at_callee source callee stp accel chunk zeros workspace
  have nextWorkspace := SszHash.Workspace.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros calleeWorkspace PackBytes.body (some (.returned returned)) actual
    (fun key different=>PackBytes.globals key source.code workspace.sha.installed different)
  let resumed := CallNormal.continuationEntry source target "pk" returned
  have resumedWorkspace := SszHash.Workspace.of_fields target resumed stp accel chunk zeros nextWorkspace rfl rfl (by intro key different; rfl)
  have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
    (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
  have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
  have currentMark := (CallNormal.continuation_lookup_other source target "pk" "mark" returned (by decide)).trans saved
  have currentLimit := (CallNormal.continuation_lookup_other source target "pk" "limit_chunks" returned (by decide)).trans limitLocal
  have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
    change target.globals.lookup (ofString "heap_ptr")=_
    rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
  have restored := after_pack_return_heap resumed final cursor out mark stp accel chunk zeros n short resumedWorkspace pk currentLimit currentOut currentMark currentHeap arena aligned value continued
  rw [endpoint]
  exact restored

/-- Actual normal payload extra-data hashing restores its entry heap before
its final length mix, which preserves that heap on every outcome. -/
theorem body_return_heap (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros : BitVec 64) (n : Nat)
    (short : n≤32) (workspace : SszHash.Workspace source stp accel chunk zeros)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextWorkspace := SszHash.Workspace.of_fields source entry stp accel chunk zeros workspace rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have restored := after_mark_return_heap entry final p cursor out cursor stp accel chunk zeros n short nextWorkspace
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "limit_chunks" (by decide)).trans limitLocal) ((other "out" (by decide)).trans output)
    (bind_lookup_same _ _ _) heap arena aligned value remaining
  rw [endpoint]
  exact restored

end InitECandidate.Solver.Input.BytesListHash

#print axioms InitECandidate.Solver.Input.BytesListHash.after_merkle_return_heap
#print axioms InitECandidate.Solver.Input.BytesListHash.after_pack_return_heap
#print axioms InitECandidate.Solver.Input.BytesListHash.after_mark_return_heap
#print axioms InitECandidate.Solver.Input.BytesListHash.body_return_heap
