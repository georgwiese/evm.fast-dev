import InitECandidate.Solver.Input.BytesListCallCost
import InitECandidate.Solver.Input.MerkleMemory
import InitECandidate.Solver.Input.MixLengthMemory
import InitECandidate.Solver.Input.PackBytesMemory
import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.HeapReleaseReturn
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScopedCallNormal

namespace InitECandidate.Solver.Input.BytesList
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch

/-- Original release-before-length-mix suffix preserves protected words. -/
theorem after_merkle_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (protection : SszHash.Protected source stp accel chunk zeros query)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMerkle=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [body_shape.2.2.2.1] at run
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "heap_release") [localVar "mark"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterRelease value (safe.summary_full source).2.1 run
  have front := HeapScope.release_call_memory source middle [localVar "mark"] query protection.workspace.sha.installed normal
  have nextProtection := SszHash.Protected.after source middle stp accel chunk zeros query protection _ none normal
    (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "heap_release") [localVar "mark"] HeapScope.releaseFormals HeapScope.releaseBody .one
      (HeapScope.release_original_code source.code protection.workspace.sha.installed) (Merkle.release_globals key source.code different))
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source middle (ofString name) (ofString "heap_release") [localVar "mark"] normal
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) mixArguments=some (MixLength.values out (BitVec.ofNat 64 n) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,mixArguments,localVar,(other "n").trans count,(other "out").trans output,MixLength.values]
  rw [body_shape.2.2.2.2] at remaining
  have mixSafe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "mix_in_length") mixArguments) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨final,mixed,returned⟩ := sequence_returned middle post _ _ value (mixSafe.summary_full middle).2.1 remaining
  have mixMemory := MixLength.call_memory middle final out (BitVec.ofNat 64 n) out chunk zeros stp accel query nextProtection outArena outAway mixArguments args mixed
  have tail := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at tail
  exact tail.trans (mixMemory.trans front)

/-- Original packed extra-data Merkle hashing and length mix preserve a protected word. -/
theorem after_pack_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (short : n≤32) (protection : SszHash.Protected source stp accel chunk zeros query)
    (packed : source.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))))
    (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have chunksBound := extra_chunks n short
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have merkleArena := AllocatedBytes.Arena.weaken _ (832+64*PackBytes.chunks n) (32*max 1 (2*PackBytes.chunks n)) temporaryArena (by omega)
  have args := merkle_arguments source cursor out n packed limitLocal output
  have safe : LocalPrefix (ofString "mark") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [body_shape.2.2.1] at run
  obtain ⟨middle,normal,remaining⟩ := sequence_returned source post _ afterMerkle value (safe.summary_full source).2.1 run
  have tempNumber : (cursor+BitVec.ofNat 64 (PackBytes.padded n)).toNat=cursor.toNat+PackBytes.padded n := byteAddress_toNat cursor (PackBytes.padded n) (by have h:=arena.upper; unfold PackBytes.padded; omega)
  have front := Merkle.call_memory source middle cursor (BitVec.ofNat 64 (PackBytes.chunks n)) 1#64 (cursor+BitVec.ofNat 64 (PackBytes.padded n)) out stp accel chunk zeros query 0 (by decide)
    (by rw [number]; change PackBytes.chunks n≤1; exact chunksBound) (by decide) protection heap
    (by rw [number]; exact packedArena) (by rw [number]; exact merkleArena) temporaryAligned outArena (by rw [tempNumber]; omega) outAway merkleArguments args normal
  have nextProtection := SszHash.Protected.after source middle stp accel chunk zeros query protection _ none normal
    (fun key different=>GlobalEffects.call_body key source.code (some none) (ofString "merkleize") merkleArguments Merkle.formals Merkle.body .one
      (Merkle.original_code source.code protection.workspace.sha.installed) (Merkle.globals key source.code protection.workspace.sha.installed different))
  have other (name : String) : middle.locals.lookup (ofString name)=source.locals.lookup (ofString name) := CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize") merkleArguments normal
  exact (after_merkle_memory middle post out stp accel chunk zeros query n nextProtection ((other "n").trans count) ((other "out").trans output) outArena outAway value remaining).trans front

/-- The real scoped pack call derives its tuple and memory frame before
passing current bindings to the observed hash/release continuation. -/
theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (short : n≤32) (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  obtain ⟨chunkBound,packedArena,temporaryArena,temporaryAligned⟩ := PBytes.packing_geometry cursor n (by omega) arena aligned
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,toExact,packArguments,localVar,pointer,count,PackBytes.values]
  obtain ⟨callee,called,pLocal,nLocal⟩ := PackBytes.environment source.code.lookup p n (PackBytes.original_code source.code protection.workspace.sha.installed)
  rw [body_shape.2.1] at run
  obtain ⟨funded,target,returned,final,actual,checked,continued,endpoint⟩ := CallNormal.scoped_normal source post "pk" PackBytes.returnShape (ofString "pack_bytes") packArguments (PackBytes.values p n)
    PackBytes.body afterPack callee PackBytes.returnShape args called value run
  have data := PackBytes.body_return_data (callEntryStateHOLFinite source callee) target cursor n (by omega) protection.workspace.sha.installed nLocal heap packedArena returned actual
  have calleeProtection := SszHash.Protected.at_callee source callee stp accel chunk zeros query protection
  have nextProtection := SszHash.Protected.after (callEntryStateHOLFinite source callee) target stp accel chunk zeros query calleeProtection PackBytes.body (some (.returned returned)) actual
    (fun key different=>PackBytes.globals key source.code protection.workspace.sha.installed different)
  let resumed := CallNormal.continuationEntry source target "pk" returned
  have resumedProtection := SszHash.Protected.of_fields target resumed stp accel chunk zeros query nextProtection rfl rfl (by intro key different; rfl)
  have pk : resumed.locals.lookup (ofString "pk")=some (PackBytes.packedValue cursor n) :=
    (CallNormal.continuation_lookup_same source target "pk" returned).trans (congrArg some data.1)
  have currentN := (CallNormal.continuation_lookup_other source target "pk" "n" returned (by decide)).trans count
  have currentLimit := (CallNormal.continuation_lookup_other source target "pk" "limit_chunks" returned (by decide)).trans limitLocal
  have currentOut := (CallNormal.continuation_lookup_other source target "pk" "out" returned (by decide)).trans output
  have currentHeap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word (cursor+BitVec.ofNat 64 (PackBytes.padded n)))) := by
    change target.globals.lookup (ofString "heap_ptr")=_
    rw [data.2,PackBytes.rounded_padded cursor n packedArena aligned]
  have packedMemory := PackBytes.body_memory (callEntryStateHOLFinite source callee) target p cursor query n (by omega) protection.workspace.sha.installed protection.workspace.sha.domain pLocal nLocal heap inputArena packedArena aligned below returned actual
  have tail := after_pack_memory resumed final cursor out stp accel chunk zeros query n short resumedProtection pk currentN currentLimit currentOut currentHeap arena aligned outArena below outAway value continued
  rw [endpoint]
  exact tail.trans packedMemory

/-- Whole original payload extra-data hash preserves protected decoded words. -/
theorem body_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (short : n≤32) (protection : SszHash.Protected source stp accel chunk zeros query)
    (pointer : source.locals.lookup (ofString "p")=some (.val (.word p)))
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (limitLocal : source.locals.lookup (ofString "limit_chunks")=some (.val (.word 1#64)))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query := by
  rw [body_shape.1] at run
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code protection.workspace.sha.installed) (some (.returned value)) run (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have nextProtection := SszHash.Protected.of_fields source entry stp accel chunk zeros query protection rfl rfl (by intro key different; rfl)
  have other (name : String) (different : ofString "mark"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have frame := after_mark_memory entry final p cursor out stp accel chunk zeros query n short nextProtection
    ((other "p" (by decide)).trans pointer) ((other "n" (by decide)).trans count) ((other "limit_chunks" (by decide)).trans limitLocal) ((other "out" (by decide)).trans output) heap inputArena arena aligned outArena below outAway value remaining
  rw [endpoint]
  exact frame

/-- Actual original three-word caller inherits the protected memory frame. -/
theorem call_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out stp accel chunk zeros query : BitVec 64) (n : Nat)
    (short : n≤32) (protection : SszHash.Protected source stp accel chunk zeros query)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (inputArena : AllocatedBytes.Arena p n) (arena : AllocatedBytes.Arena cursor (832+96*PackBytes.chunks n)) (aligned : cursor.toNat%8=0) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (values p n out))
    (run : evaluateHOLFiniteState source (.call (some (none,none)) (ofString "htr_bytes_list") arguments)=(none,post)) : post.memory query=source.memory query := by
  obtain ⟨callee,called,pLocal,nLocal,limitCell,outLocal⟩ := environment source.code.lookup p n out (original_code source.code protection.workspace.sha.installed)
  exact MemoryAt.call_normal source post (ofString "htr_bytes_list") arguments (values p n out) body callee .one query args called
    (fun target value evaluated=>body_memory (callEntryStateHOLFinite source callee) target p cursor out stp accel chunk zeros query n short
      (SszHash.Protected.at_callee source callee stp accel chunk zeros query protection) pLocal nLocal limitCell outLocal heap inputArena arena aligned outArena below outAway value evaluated) run

end InitECandidate.Solver.Input.BytesList

#print axioms InitECandidate.Solver.Input.BytesList.after_pack_memory
#print axioms InitECandidate.Solver.Input.BytesList.after_mark_memory
#print axioms InitECandidate.Solver.Input.BytesList.body_memory

#print axioms InitECandidate.Solver.Input.BytesList.call_memory

#print axioms InitECandidate.Solver.Input.BytesList.after_merkle_memory
