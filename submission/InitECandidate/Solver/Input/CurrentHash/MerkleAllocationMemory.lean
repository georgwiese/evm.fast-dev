import InitECandidate.Solver.Input.CurrentHash.MerkleBufferMemory
import InitECandidate.Solver.Input.CurrentHash.MarkedHeap
import InitECandidate.Solver.WitnessRadix.AllocationCallNormal

namespace InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix WitnessRadix.QueryBranch
open MerkleAllocationCost
open MerkleBufferCost (afterSize afterMark afterZero afterBuffer)

/-- The same normal allocation derives real persistent room and the buffer
arena used by the actual fill/hash suffix. No room is an entry premise. -/
theorem allocated_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out query : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (size : source.locals.lookup (ofString "size")=some (.val (.word (BitVec.ofNat 64 (2^depth)))))
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (inside : n≤2^depth) (small : 32*2^depth+32<2^64) (targetSmall : target<2^63) (depths : depth≤target)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterSize=(some (.returned value),post)) : post.memory query=source.memory query := by
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) [amountExpression] =
      some (PersistentAlloc.values (BitVec.ofNat 64 (32*2^depth))) := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,amountExpression,localVar,size,PersistentAlloc.values,
      valueIsWord,valueWord,panOpHOL,BitVec.ofNat_mul,Nat.mul_comm]
  rw [source_shape.2.2] at actual
  obtain ⟨room,positive,inner,remaining,endpoint⟩ := PersistentAlloc.call_normal source post "buf" [amountExpression] afterBuffer cursor
    (BitVec.ofNat 64 (32*2^depth)) args (PersistentAlloc.original_code source.code installed) (Trap.original_code source.code installed)
    heap heapBound value actual
  have amountNumber : (BitVec.ofNat 64 (32*2^depth)).toNat = 32*2^depth := by
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  rw [amountNumber] at room
  have arena : AllocatedBytes.Arena cursor (32*2^depth) := ⟨heapLower,by omega⟩
  let allocated := PersistentAlloc.post {source with clock:=source.clock-1} cursor (BitVec.ofNat 64 (32*2^depth))
  let entry := bind allocated "buf" cursor
  have kept (name : String) (different : ofString "buf"≠ofString name) : entry.locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
    bind_lookup_other allocated "buf" name cursor different
  have locals : MerkleBufferCost.Locals entry p cursor n (2^depth) depth target := ⟨(kept "p" (by decide)).trans data.pointer,
    bind_lookup_same _ _ _,(kept "n" (by decide)).trans data.count,(kept "size" (by decide)).trans size,
    (kept "dn" (by decide)).trans data.dn,(kept "target" (by decide)).trans data.maximum⟩
  have pointers : MerkleSuffixMemory.Pointers entry cursor out := ⟨installed,domain,bind_lookup_same _ _ _,(kept "out" (by decide)).trans output⟩
  have frame := MerkleBufferMemory.memory entry inner p cursor out query n (2^depth) depth target locals pointers (Nat.two_pow_pos depth) inside
    (by omega) targetSmall depths inputArena arena outArena aligned
    (CopyGeneral.Away.after cursor query (32*2^depth) aligned (by omega) below) outAway value remaining
  rw [endpoint]
  exact frame

theorem sized_memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out query : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depthSmall : depth<64) (inside : n≤2^depth) (small : 32*2^depth+32<2^64) (targetSmall : target<2^63) (depths : depth≤target)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterMark=(some (.returned value),post)) : post.memory query=source.memory query := by
  rw [source_shape.2.1] at actual
  obtain ⟨inner,normal,endpoint⟩ := declaration_return_word source post "size" sizeExpression (BitVec.ofNat 64 (2^depth)) afterSize value
    (size_read source depth depthSmall data.dn) actual
  let entry := bind source "size" (BitVec.ofNat 64 (2^depth))
  have kept (name : String) (different : ofString "size"≠ofString name) := bind_lookup_other source "size" name (BitVec.ofNat 64 (2^depth)) different
  have next : Params entry p n depth target := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.count,
    (kept "dn" (by decide)).trans data.dn,(kept "target" (by decide)).trans data.maximum⟩
  have frame := allocated_memory entry inner p cursor out query n depth target next installed domain (bind_lookup_same _ _ _)
    ((kept "out" (by decide)).trans output) inside small targetSmall depths heap heapLower heapBound aligned inputArena outArena below outAway value normal
  rw [endpoint]
  exact frame

/-- Whole nonempty current Merkle scope. Its actual allocation supplies room;
the genuine final release restores the entering heap and protected metadata. -/
theorem memory (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (p cursor out query : BitVec 64) (n depth target : Nat)
    (data : Params source p n depth target) (installed : OriginalCode.Installed source.code) (domain : source.memaddrs=InitE.ordinaryDomain)
    (output : source.locals.lookup (ofString "out")=some (.val (.word out)))
    (depthSmall : depth<64) (inside : n≤2^depth) (small : 32*2^depth+32<2^64) (targetSmall : target<2^63) (depths : depth≤target)
    (heap : source.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)))
    (heapLower : 2701131776≤cursor.toNat) (heapBound : cursor.toNat≤2952790016) (aligned : cursor.toNat%8=0)
    (inputArena : AllocatedBytes.Arena p (32*n)) (outArena : AllocatedBytes.Arena out 32)
    (below : query.toNat<cursor.toNat) (outAway : CopyGeneral.Away out query 32)
    (value : ValueHOL 64) (actual : evaluateHOLFiniteState source afterZero=(some (.returned value),post)) :
    post.memory query=source.memory query ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word cursor)) := by
  have restored := MarkedHeap.merkle_nonempty source post cursor installed heap value actual
  rw [source_shape.1] at actual
  obtain ⟨positive,inner,normal,endpoint⟩ := HeapScope.mark_call_trace source post cursor "mark" afterMark heap
    (HeapScope.mark_original_code source.code installed) (some (.returned value)) actual (by simp)
  let entry := bind {source with clock:=source.clock-1} "mark" cursor
  have kept (name : String) (different : ofString "mark"≠ofString name) := bind_lookup_other {source with clock:=source.clock-1} "mark" name cursor different
  have next : Params entry p n depth target := ⟨(kept "p" (by decide)).trans data.pointer,(kept "n" (by decide)).trans data.count,
    (kept "dn" (by decide)).trans data.dn,(kept "target" (by decide)).trans data.maximum⟩
  have frame := sized_memory entry inner p cursor out query n depth target next installed domain
    ((kept "out" (by decide)).trans output) depthSmall inside small targetSmall depths heap heapLower heapBound aligned inputArena outArena below outAway value normal
  refine ⟨?_,restored⟩
  rw [endpoint]
  exact frame

end InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory

#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory.allocated_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory.sized_memory
#print axioms InitECandidate.Solver.Input.CurrentHash.MerkleAllocationMemory.memory
