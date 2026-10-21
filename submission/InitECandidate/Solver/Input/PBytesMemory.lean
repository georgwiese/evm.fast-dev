import InitECandidate.Solver.Input.PBytesCallCost
import InitECandidate.Solver.Input.PListChunksMemory
import InitECandidate.Solver.Input.PackBytesMemory
import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.HeapReleaseReturn
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.PBytes
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Actual original packed-list hashing and release preserve a protected word. -/
theorem after_pack_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (small : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := packing_geometry cursor n small arena aligned
  have args := list_arguments source cursor out n packed count output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "htr_plist_chunks") listArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterList value (safe.summary_full source).2.1 run
  have tempNumber : (cursor+BitVec.ofNat 64 (PackBytes.padded n)).toNat=cursor.toNat+PackBytes.padded n :=
    byteAddress_toNat cursor (PackBytes.padded n) (by have upper:=arena.upper; unfold PackBytes.padded; omega)
  have front := PListChunks.call_memory source middle cursor (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out (BitVec.ofNat 64 n) stp accel chunk zeros query (PackBytes.chunks n)
    chunkBound protection heap packedArena temporaryArena temporaryAligned outArena (by rw [tempNumber]; omega) outAway listArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have tail := HeapScope.release_return_memory middle post [localVar "mark"] query (fields.2.2.2.symm ▸ protection.workspace.sha.installed) value remaining
  exact tail.trans front

/-- The real scoped pack call derives its tuple and memory frame before
passing current bindings to the observed hash/release continuation. -/
theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (small : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := packing_geometry cursor n small arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code protection.workspace.sha.installed)
  obtain ⟨funded,target,returned,final,actual,checked,continued,endpoint⟩ := CallNormal.scoped_normal source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n)
    PackBytes.body afterPack callee PackBytes.returnShape args called value run
  have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n small protection.workspace.sha.installed nLocal heap packedArena returned actual
  have calleeProtection := SszHash.Protected.at_callee source callee stp accel chunk zeros query protection
  have nextProtection := SszHash.Protected.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros query calleeProtection PackBytes.body (some (.returned returned)) actual
    (fun key different=>PackBytes.globals key source.code protection.workspace.sha.installed different)
  let resumed := CallNormal.continuationEntry source target "pk" returned
  have resumedProtection := SszHash.Protected.of_fields target resumed stp accel chunk zeros query nextProtection rfl rfl (by intro key different; rfl)
  have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
    (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
  have currentN := (CallNormal.continuation_lookup_other source target "pk" "n" returned (by decide)).trans count
  have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
  have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
    change target.globals.lookup (ofString "heap_ptr")=_
    rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
  have packedMemory := PackBytes.body_memory (callEntryStateHOLFinite source callee) target p cursor query n small protection.workspace.sha.installed protection.workspace.sha.domain pLocal nLocal heap inputArena packedArena aligned below returned actual
  have tail := after_pack_memory resumed final cursor out stp accel chunk zeros query n small resumedProtection pk currentN currentOut currentHeap arena aligned outArena below outAway value continued
  rw [endpoint]
  exact tail.trans packedMemory

/-- Whole unchanged progressive byte-list hash preserves protected decoded
words through packing, hashing, length mixing and release. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (small : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  rw [body_shape] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have frame := after_mark_memory entry final p cursor out stp accel chunk zeros query n small nextProtection
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "out" (by decide)).trans output) heap inputArena arena aligned outArena below outAway value remaining
  rw [endpoint]
  exact frame

/-- Actual original three-word caller inherits the protected memory frame. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (small : n≤134217728) (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_pbytes") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal,outLocal⟩ := environment source.code.lookup p n out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_pbytes") arguments (values p n out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros query n small
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) pLocal nLocal outLocal heap inputArena arena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.PBytes

#print axioms InitECandidate.Solver.Input.PBytes.after_pack_memory
#print axioms InitECandidate.Solver.Input.PBytes.after_mark_memory
#print axioms InitECandidate.Solver.Input.PBytes.body_memory

#print axioms InitECandidate.Solver.Input.PBytes.call_memory
