import InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory
import InitECandidate.Solver.Input.CurrentHash.MerkleMemory
import InitECandidate.Solver.Input.CurrentHash.Merkleize
import InitECandidate.Solver.Input.CurrentHash.MixMemory
import InitECandidate.Solver.Input.CurrentHash.ByteHeap
import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.BytesListMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open BytesListCost

theorem after_merkle_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (out chunk query : BitVec 64) (n : Nat)
    (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (count : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 n))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out))) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMerkle=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [source_shape.2.2.2] at actual
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .heap_release) [localVar "mark"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have front := HeapScope.release_call_memory source middle [localVar "mark"] query installed normal
  have fields := evaluation_fields source middle _ none normal
  have currentCode : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact installed
  have global := GlobalEffects.call_body (key .lengthChunk) source.code (some none) (Code.name .heap_release) [localVar "mark"]
    (Code.formals .heap_release) (Code.body .heap_release) (Code.shape .heap_release) (Code.installed source.code installed .heap_release)
    (SharedEffects.HeapRelease.preserves .lengthChunk source.code installed) source rfl
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (.call (some (none,none)) (Code.name .heap_release) [localVar "mark"])).2 = _ at global
  rw [normal] at global
  have currentChunk : middle.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)) := (congrArg Prod.snd global).trans chunkCell
  have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (Code.name .heap_release) [localVar "mark"] normal
  have args : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) [localVar "out",localVar "n",localVar "out"] =
      some [.val (.word out),.val (.word (BitVec.ofNat 64 n)),.val (.word out)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,(kept "out").trans output,(kept "n").trans count]
  have mixSafe : LocalPrefix (ofString "out") (.call (some (none,none)) (Code.name .mix_in_length) [localVar "out",localVar "n",localVar "out"]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨final,mixed,returned⟩ := Input.sequence_returned middle post _ _ value (mixSafe.summary_full middle).2.1 remaining
  have mixedMemory := MixMemory.call_memory middle final out (BitVec.ofNat 64 n) chunk out query currentCode (fields.1.trans domain)
    currentChunk chunkArena chunkAligned chunkAway outAway _ args mixed
  have tail := MemoryAt.return_current final (.const 0#64) query
  rw [returned] at tail
  exact tail.trans (mixedMemory.trans front)

theorem after_pack_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer cursor limit out zeros chunk query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p limit out n)
    (pk : source.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple buffer n))
    (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget) (limitBound : limit.toNat≤2^budget)
    (bufferArena : AllocatedBytes.Arena buffer (PackBytes.padded n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) : post.memory query=source.memory query := by
  have power : 2^budget≤2^57 := Nat.pow_le_pow_right (by decide) (by omega)
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) merkleArguments =
      some (Merkle.values buffer (BitVec.ofNat 64 (PackBytes.chunks n)) limit out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,merkleArguments,localVar,pk,PackBytesReturn.tuple,data.maximum,data.output,Merkle.values]
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [source_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := MerkleMemory.call_memory source middle buffer (BitVec.ofNat 64 (PackBytes.chunks n)) limit out cursor zeros query budget context small
    (by rw [number]; exact chunksBound) limitBound (by simpa only [number,PackBytes.padded] using bufferArena) outArena outAway merkleArguments args normal
  have global := GlobalEffects.call_body (key .lengthChunk) source.code (some none) (Code.name .merkleize) merkleArguments
    (Code.formals .merkleize) (Code.body .merkleize) (Code.shape .merkleize) (Code.installed source.code context.installed .merkleize)
    (Merkleize.preserves .lengthChunk source.code context.installed) source rfl
  change GlobalEffects.erase (key .lengthChunk) (evaluateHOLFiniteState source (.call (some (none,none)) (ofString "merkleize") merkleArguments)).2 = _ at global
  rw [normal] at global
  have kept (name : String) := CallNormal.ignored_lookup source middle (ofString name) (ofString "merkleize") merkleArguments normal
  have fields := evaluation_fields source middle _ none normal
  have currentCode : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact context.installed
  exact (after_merkle_memory middle post out chunk query n currentCode (fields.1.trans context.domain)
    ((congrArg Prod.snd global).trans chunkCell) chunkArena chunkAligned chunkAway ((kept "n").trans data.length)
    ((kept "out").trans data.output) outAway value remaining).trans frame

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor limit out zeros chunk query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p limit out n)
    (lengthSmall : n+64<2^64) (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget) (limitBound : limit.toNat≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,packArguments,localVar,data.pointer,data.length,PackBytes.values]
  rw [source_shape.2.1] at actual
  obtain ⟨target,final,image,codeEq,domainEq,globals,remaining,endpoint⟩ := PackBytesScopeMemory.image source post p cursor query n lengthSmall context.installed context.domain
    context.heap context.heapLower context.heapBound context.aligned inputArena context.below "pk" packArguments afterPack args value actual
  let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple cursor n)
  let nextCursor := PersistentAlloc.rounded cursor (BitVec.ofNat 64 (PackBytes.padded n))
  have kept (name : String) (different : ofString "pk"≠ofString name) := CallNormal.continuation_lookup_other source target "pk" name (PackBytesReturn.tuple cursor n) different
  have nextData : Params entry p limit out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,
    (kept "limit_chunks" (by decide)).trans data.maximum,(kept "out" (by decide)).trans data.output⟩
  have pk : entry.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple cursor n) := CallNormal.continuation_lookup_same _ _ _ _
  have nextCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact context.installed
  have next : MerkleMemory.Context entry nextCursor zeros query := ⟨nextCode,domainEq.trans context.domain,(globals .zeroHashes).trans context.zeroCell,
    context.zeroArena,image.heap,by have h:=image.grows; have l:=context.heapLower; dsimp [nextCursor]; omega,image.nextBound,image.nextAligned,
    by have h:=image.grows; have l:=context.below; dsimp [nextCursor]; omega⟩
  have bufferArena : AllocatedBytes.Arena cursor (PackBytes.padded n) := ⟨context.heapLower,by have h:=image.room; omega⟩
  have frame := after_pack_memory entry final p cursor nextCursor limit out zeros chunk query n budget next nextData pk small chunksBound limitBound
    bufferArena outArena outAway ((globals .lengthChunk).trans chunkCell) chunkArena chunkAligned chunkAway value remaining
  rw [endpoint]
  exact frame.trans image.protectedWord

/-- Complete unchanged byte-list hashing retains earlier metadata and restores
its actual entering heap. Every allocation and callee return is from this run. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor limit out zeros chunk query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p limit out n)
    (lengthSmall : n+64<2^64) (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget) (limitBound : limit.toNat≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (chunkCell : source.globals.lookup (ofString "ssz_len_chunk")=some (.val (.word chunk)))
    (chunkArena : AllocatedBytes.Arena chunk 32) (chunkAligned : chunk.toNat%8=0) (chunkAway : CopyGeneral.Away chunk query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have heap := ByteHeap.list source post cursor context.installed context.heap value actual
  rw [source_shape.1] at actual
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have nextData : Params entry p limit out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,
    (kept "limit_chunks" (by decide)).trans data.maximum,(kept "out" (by decide)).trans data.output⟩
  have next : MerkleMemory.Context entry cursor zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have frame := after_mark_memory entry final p cursor limit out zeros chunk query n budget next nextData lengthSmall small chunksBound limitBound
    inputArena outArena outAway chunkCell chunkArena chunkAligned chunkAway value remaining
  refine ⟨?_,heap⟩
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.BytesListMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListMemory.after_merkle_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListMemory.after_pack_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListMemory.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesListMemory.body_frame
