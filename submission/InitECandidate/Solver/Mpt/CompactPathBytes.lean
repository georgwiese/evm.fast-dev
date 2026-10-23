import InitECandidate.Solver.Mpt.TriePathBytes
import InitECandidate.Solver.Mpt.CompactToNibblesSnapshotNibbles

namespace InitECandidate.Solver.Mpt.CompactToNibbles
open Flapjack PanSemStateFiniteExact WitnessRadix

/-- The actual compact allocation and proven byte range establish full
stored-path mapping, including bytes beyond the traversal's short query. -/
theorem Snapshot.nibble_span (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap cursor limit : BitVec 64) (count : Nat) (leaf : BitVec 64)
    (snapshot : Snapshot source target length heap cursor limit count leaf) (range : KeyToNibbles.NibblePrefix target heap count) :
    TrieWalk.NibbleSpan target.memory target.memaddrs target.be heap count := by
  refine ⟨by have upper:=snapshot.outputArena.upper; have bound:=snapshot.nibbleBound; omega,?_,?_⟩
  · intro offset inside
    exact AllocatedBytes.byte_mapped target heap (2*length) offset snapshot.arena.domain snapshot.outputArena (inside.trans_le snapshot.nibbleBound)
  · change KeyToNibbles.NibblePrefix target heap count
    exact range

theorem Snapshot.nibble_extent (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap cursor limit : BitVec 64) (count : Nat) (leaf : BitVec 64)
    (snapshot : Snapshot source target length heap cursor limit count leaf) :
    heap.toNat+count≤(PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat := by
  have bound:=snapshot.nibbleBound
  have grows:=snapshot.grows
  omega

/-- Later real allocations above this compact output preserve the full
stored-path bytes via their old-memory frame, including partial words. -/
theorem Snapshot.nibble_span_after (origin source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (length : Nat) (heap cursor limit : BitVec 64) (count : Nat) (leaf : BitVec 64)
    (snapshot : Snapshot origin source length heap cursor limit count leaf) (range : KeyToNibbles.NibblePrefix source heap count)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<(PersistentAlloc.rounded heap (BitVec.ofNat 64 (2*length))).toNat → target.memory query=source.memory query) :
    TrieWalk.NibbleSpan target.memory target.memaddrs target.be heap count :=
  (snapshot.nibble_span origin source length heap cursor limit count leaf range).of_before source target heap count _
    (snapshot.nibble_extent origin source length heap cursor limit count leaf) domain endian memory

end InitECandidate.Solver.Mpt.CompactToNibbles

#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.Snapshot.nibble_span
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.Snapshot.nibble_extent
#print axioms InitECandidate.Solver.Mpt.CompactToNibbles.Snapshot.nibble_span_after
