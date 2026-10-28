import InitECandidate.Solver.Input.CurrentHash.PackBytesScopeMemory
import InitECandidate.Solver.Input.CurrentHash.MerkleMemory
import InitECandidate.Solver.Input.CurrentHash.ByteHeap
import InitECandidate.Solver.Input.HeapReleaseMemory
import InitECandidate.Solver.Input.CopyReturnMemory
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open BytesVectorCost

theorem after_pack_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p buffer cursor out zeros query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (pk : source.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple buffer n))
    (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget)
    (bufferArena : AllocatedBytes.Arena buffer (PackBytes.padded n)) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterPack=(some (.returned value),post)) : post.memory query=source.memory query := by
  have power : 2^budget≤2^57 := Nat.pow_le_pow_right (by decide) (by omega)
  have number : (BitVec.ofNat 64 (PackBytes.chunks n)).toNat=PackBytes.chunks n := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) merkleArguments =
      some (Merkle.values buffer (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) out) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,merkleArguments,localVar,pk,PackBytesReturn.tuple,data.output,Merkle.values]
  have safe : LocalPrefix (ofString "out") (.call (some (none,none)) (ofString "merkleize") merkleArguments) := .call none _ _ (by intro name impossible; cases impossible)
  rw [source_shape.2.2.1] at actual
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have frame := MerkleMemory.call_memory source middle buffer (BitVec.ofNat 64 (PackBytes.chunks n)) (BitVec.ofNat 64 (PackBytes.chunks n)) out cursor zeros query budget context small
    (by rw [number]; exact chunksBound) (by rw [number]; exact chunksBound)
    (by simpa only [number,PackBytes.padded] using bufferArena) outArena outAway merkleArguments args normal
  have fields := evaluation_fields source middle _ none normal
  have currentCode : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact context.installed
  rw [source_shape.2.2.2] at remaining
  exact (HeapScope.release_return_memory middle post [localVar "mark"] query currentCode value remaining).trans frame

theorem after_mark_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out zeros query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (lengthSmall : n+64<2^64) (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) packArguments=some (PackBytes.values p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,packArguments,localVar,data.pointer,data.length,PackBytes.values]
  rw [source_shape.2.1] at actual
  obtain ⟨target,final,image,codeEq,domainEq,globals,remaining,endpoint⟩ := PackBytesScopeMemory.image source post p cursor query n lengthSmall context.installed context.domain
    context.heap context.heapLower context.heapBound context.aligned inputArena context.below "pk" packArguments afterPack args value actual
  let entry := CallNormal.continuationEntry source target "pk" (PackBytesReturn.tuple cursor n)
  let nextCursor := PersistentAlloc.rounded cursor (BitVec.ofNat 64 (PackBytes.padded n))
  have kept (name : String) (different : ofString "pk"≠ofString name) := CallNormal.continuation_lookup_other source target "pk" name (PackBytesReturn.tuple cursor n) different
  have nextData : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,(kept "out" (by decide)).trans data.output⟩
  have pk : entry.locals.lookup (ofString "pk")=some (PackBytesReturn.tuple cursor n) := CallNormal.continuation_lookup_same _ _ _ _
  have nextCode : OriginalCode.Installed entry.code := by change OriginalCode.Installed target.code; rw [codeEq]; exact context.installed
  have next : MerkleMemory.Context entry nextCursor zeros query := ⟨nextCode,domainEq.trans context.domain,(globals .zeroHashes).trans context.zeroCell,
    context.zeroArena,image.heap,by have h:=image.grows; have l:=context.heapLower; dsimp [nextCursor]; omega,image.nextBound,image.nextAligned,
    by have h:=image.grows; have l:=context.below; dsimp [nextCursor]; omega⟩
  have bufferArena : AllocatedBytes.Arena cursor (PackBytes.padded n) := ⟨context.heapLower,by have h:=image.room; omega⟩
  have frame := after_pack_memory entry final p cursor nextCursor out zeros query n budget next nextData pk small chunksBound bufferArena outArena outAway value remaining
  rw [endpoint]
  exact frame.trans image.protectedWord

theorem long_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out zeros query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (lengthSmall : n+64<2^64) (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source long=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [source_shape.1] at actual
  obtain ⟨paid,final,remaining,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark context.heap
    (HeapScope.mark_original_code source.code context.installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have nextData : Params entry p out n := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.length,(kept "out" (by decide)).trans data.output⟩
  have next : MerkleMemory.Context entry cursor zeros query := ⟨context.installed,context.domain,context.zeroCell,context.zeroArena,context.heap,
    context.heapLower,context.heapBound,context.aligned,context.below⟩
  have frame := after_mark_memory entry final p cursor out zeros query n budget next nextData lengthSmall small chunksBound inputArena outArena outAway value remaining
  rw [endpoint]
  exact frame

theorem short_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p out query : BitVec 64) (n : Nat)
    (short : n≤32) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (data : Params source p out n) (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32)
    (aligned : out.toNat%8=0) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source shortBody=(some (.returned value),post)) : post.memory query=source.memory query := by
  unfold shortBody at actual
  have safe : LocalPrefix (ofString "p") (.call (some (none,none)) (ofString "memzero") [localVar "out",.const 32#64]) := .call none _ _ (by intro name impossible; cases impossible)
  obtain ⟨middle,normal,remaining⟩ := Input.sequence_returned source post _ _ value (safe.summary_full source).2.1 actual
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [localVar "out",.const 32#64]=some (Zero.values out 32) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,data.output,Zero.values]
  have front := MemoryAt.zero_normal source middle _ out query 32 args installed domain outArena aligned (by decide) (by intro offset inside; exact (outAway offset inside).1) normal
  have next := data.after_call _ _ normal
  have copyArgs : evalListHOLFinite middle (h:=fun address=>Classical.propDecidable (middle.memaddrs address)) [localVar "out",localVar "p",localVar "n"]=some (CopyGeneral.values out p n) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,next.output,next.pointer,next.length,CopyGeneral.values]
  have fields := evaluation_fields source middle _ none normal
  have currentCode : OriginalCode.Installed middle.code := by rw [fields.2.2.2]; exact installed
  exact (MemoryAt.copy_returned middle post _ p out query n currentCode (fields.1.trans domain) copyArgs inputArena
    (AllocatedBytes.Arena.weaken out 32 n outArena short) (by intro offset inside; exact outAway offset (by omega)) value remaining).trans front

/-- Both actual vector branches preserve earlier metadata and restore their
entering heap; the short branch writes only its real32-byte caller output. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out zeros query : BitVec 64) (n budget : Nat)
    (context : MerkleMemory.Context source cursor zeros query) (data : Params source p out n)
    (lengthSmall : n+64<2^64) (small : budget<58) (chunksBound : PackBytes.chunks n≤2^budget)
    (inputArena : AllocatedBytes.Arena p n) (outArena : AllocatedBytes.Arena out 32) (outAligned : out.toNat%8=0) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source body=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have heap := ByteHeap.vector source post cursor context.installed context.heap value actual
  refine ⟨?_,heap⟩
  by_cases short : n≤32
  · have stops := (show NoFallthrough shortBody from .sequence _ _ (.sequence _ _ (.returned _))) source
    rw [body_shape,evaluateHOLFiniteState_seq_line780,guard_run source n (by omega) data.length,if_pos short] at actual
    generalize computed : evaluateHOLFiniteState source shortBody=observed at actual stops
    obtain ⟨result,middle⟩ := observed
    cases result with
    | none => exact False.elim (stops rfl)
    | some result => exact short_memory source post p out query n short context.installed context.domain data inputArena outArena outAligned outAway value (computed.trans actual)
  · rw [body_shape,StateSteps.next_sequence source source _ _ (by rw [guard_run source n (by omega) data.length,if_neg short]) (Nat.le_refl _)] at actual
    exact long_memory source post p cursor out zeros query n budget context data lengthSmall small chunksBound inputArena outArena outAway value actual

end InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory.after_pack_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory.after_mark_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory.long_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory.short_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.BytesVectorMemory.body_frame
