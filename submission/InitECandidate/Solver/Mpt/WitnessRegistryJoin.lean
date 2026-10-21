import InitECandidate.Solver.Mpt.TrieGraphUnion
import InitECandidate.Solver.Mpt.TrieWalkValuesMap
import InitECandidate.Solver.Mpt.WitnessMaterializeRichOutput
import InitECandidate.Solver.Mpt.WitnessCoreStablePrefix

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

def ValueView.widen {memory : Memory} {domain : BitVec 64 → Prop}
    {node pointerOffset lengthOffset : BitVec 64} {small large : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (view : ValueView memory domain node pointerOffset lengthOffset small property) (bound : small≤large) :
    ValueView memory domain node pointerOffset lengthOffset large property :=
  {view with payload:=⟨view.payload.1.trans bound,view.payload.2⟩}

def Values.widen {memory : Memory} {domain : BitVec 64 → Prop}
    {graph : Graph memory domain} {small large : Nat} {property : BitVec 64 → BitVec 64 → Prop}
    (values : Values graph small property) (bound : small≤large) : Values graph large property :=
  ⟨fun node member active tag=>(values.leaf node member active tag).widen bound,
    fun node member active a b c=>(values.branch node member active a b c).widen bound⟩

end InitECandidate.Solver.Mpt.TrieWalk

namespace InitECandidate.Solver.Mpt.WitnessMaterialize
open Flapjack PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString
open WitnessCore WitnessCore.Stack

/-- Preserve a caller's closed graph below the real incoming heap, then
join the actual fresh decoded graph above it. Stored-value lifetime
predicates may be weakened to the caller's current predicate; no old
value is required to lie in the witness input database. -/
theorem RichOutput.join_registry (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (db heap : BitVec 64) (returned : ValueHOL 64) (lower limit : Nat)
    (output : RichOutput input heap.toNat db post returned) (memory : StablePrefix source post heap.toNat)
    (domain : post.memaddrs=source.memaddrs) (old : TrieWalk.Graph source.memory source.memaddrs)
    (property : BitVec 64 → BitVec 64 → Prop) (oldValues : TrieWalk.Values old limit property)
    (oldRegions : old.Regions lower heap.toNat) (oldDisjoint : old.Disjoint)
    (floor : 2713717616≤lower) (ordered : lower≤heap.toNat) (bounded : 1024≤limit)
    (extra : ∀ pointer length,WitnessValue db pointer length → property pointer length) :
    ∃ nextHeap node,returned=.val (.word node) ∧ post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      ∃ graph : TrieWalk.Graph post.memory post.memaddrs,
        Nonempty (TrieWalk.Values graph limit property) ∧ graph.Regions lower nextHeap.toNat ∧ graph.Disjoint ∧
        (∀ child,old.valid child → graph.valid child) ∧ graph.valid node := by
  obtain ⟨kept,same,keptRegions,keptDisjoint,⟨keptValues⟩⟩:=old.after_agreement source post limit lower heap.toNat property oldValues oldRegions oldDisjoint domain
    (by intro query needed; have bounds:=old.footprint_bounds lower heap.toNat oldRegions query needed; exact memory query (floor.trans bounds.1) bounds.2)
    (by intro query needed; have bounds:=old.value_bounds lower heap.toNat oldRegions query needed; exact memory query (floor.trans bounds.1) bounds.2)
  obtain ⟨actualHeap,child,valueEq,heapCell,registry,member⟩:=output.2
  have physical:=output.1
  obtain ⟨physicalHeap,physicalChild,physicalValue,physicalCell,arena,aligned,grows,rest⟩:=physical
  have sameHeap : physicalHeap=actualHeap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (physicalCell.symm.trans heapCell)))
  subst physicalHeap
  let graph:=kept.union registry.graph
  have freshValues : TrieWalk.Values registry.graph limit property:=
    (registry.values.map_extra post.memory post.memaddrs registry.graph 1024 (WitnessValue db) property extra).widen bounded
  refine ⟨actualHeap,child,valueEq,heapCell,graph,⟨TrieWalk.Values.union kept registry.graph limit property keptValues freshValues⟩,
    keptRegions.union kept registry.graph lower heap.toNat actualHeap.toNat registry.regions ordered grows,
    keptDisjoint.union kept registry.graph lower heap.toNat actualHeap.toNat keptRegions registry.regions registry.disjoint,?_,Or.inr member⟩
  intro child known
  exact Or.inl (by rw [same]; exact known)

end InitECandidate.Solver.Mpt.WitnessMaterialize

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueView.widen
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.widen
#print axioms InitECandidate.Solver.Mpt.WitnessMaterialize.RichOutput.join_registry
