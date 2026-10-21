import InitECandidate.Solver.Mpt.WitnessDecodeResult
import InitECandidate.Solver.Mpt.WitnessCoreReturnCache

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString

/-- The materializer's current nonnull result owns its header/cache
words, has an actual constructor tag and follows the waiting parent's
allocation frontier. Rich path/value/child views are retained separately. -/
structure ResultNode (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) (node : BitVec 64) : Prop where
  arena : AllocatedBytes.Arena node 32
  aligned : node.toNat%8=0
  fresh : lower≤node.toNat
  before : node.toNat+32≤upper
  kind : ∃ tag : BitVec 64,source.memory node=.word tag ∧ tag.toNat≤3

def ResultOwned (source : PanSemStateFiniteExact 64 Guest.HostMemory) (lower upper : Nat) (node : BitVec 64) : Prop:=
  node=0#64 ∨ ResultNode source lower upper node

theorem ResultNode.of_region (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node tag : BitVec 64)
    (size lower upper : Nat) (arena : AllocatedBytes.Arena node size) (sizeBound : 32≤size)
    (aligned : node.toNat%8=0) (fresh : lower≤node.toNat) (before : node.toNat+size≤upper)
    (kind : source.memory node=.word tag) (tagBound : tag.toNat≤3) : ResultNode source lower upper node := by
  have arenaUpper:=arena.upper
  exact ⟨⟨arena.lower,by omega⟩,aligned,fresh,by omega,tag,kind,tagBound⟩

theorem ResultNode.weaken (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (lower upper smaller larger : Nat) (owned : ResultNode source lower upper node) (first : smaller≤lower) (last : upper≤larger) :
    ResultNode source smaller larger node :=
  ⟨owned.arena,owned.aligned,first.trans owned.fresh,owned.before.trans last,owned.kind⟩

theorem ResultOwned.cache_geometry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper node) :
    node=0#64 ∨ AllocatedBytes.Arena node 32 ∧ node.toNat%8=0 := by
  rcases owned with zero|allocated
  · exact Or.inl zero
  · exact Or.inr ⟨allocated.arena,allocated.aligned⟩

theorem ResultOwned.cache (source : PanSemStateFiniteExact 64 Guest.HostMemory) (node hash : BitVec 64)
    (lower upper : Nat) (owned : ResultOwned source lower upper node) :
    ResultOwned (returnCacheState source node hash) lower upper node := by
  rcases owned with zero|allocated
  · exact Or.inl zero
  · have away : node≠node+24#64:=by
      intro same
      have equal : (0#64 : BitVec 64)=24#64:=(BitVec.add_right_inj node).mp (by simpa only [BitVec.add_zero] using same)
      exact (by decide : (0#64 : BitVec 64)≠24#64) equal
    obtain ⟨tag,tagCell,tagBound⟩:=allocated.kind
    exact Or.inr ⟨allocated.arena,allocated.aligned,allocated.fresh,allocated.before,tag,
      (return_cache_memory source node hash node away).trans tagCell,tagBound⟩

/-- A genuine terminal decoder result is null or a fresh physical leaf,
with its real current heap. This consumes the actual returned result and
global cell; it assumes no future successful parse/allocation. -/
theorem decode_result_owned (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db pointer length heap cursor limit node finalHeap : BitVec 64)
    (result : WitnessDecode.NormalResult post db pointer length heap cursor limit (.rStruct [.val (.word 0#64),.val (.word node)]))
    (heapCell : post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap))) :
    ResultOwned post heap.toNat finalHeap.toNat node := by
  cases result with
  | empty scratch=>exact Or.inl rfl
  | leaf node nibbles nibbleLength valuePointer valueLength actualHeap view freshPath freshNode scratch actualCell heapArena heapAligned nodeBefore=>
    have same : actualHeap=finalHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
    subst actualHeap
    exact Or.inr (ResultNode.of_region post node 1#64 64 heap.toNat finalHeap.toNat view.arena (by decide) view.aligned freshNode nodeBefore view.tag (by decide))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultNode.of_region
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultNode.weaken
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultOwned.cache_geometry
#print axioms InitECandidate.Solver.Mpt.WitnessCore.ResultOwned.cache
#print axioms InitECandidate.Solver.Mpt.WitnessCore.decode_result_owned
