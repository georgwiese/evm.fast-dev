import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions
import InitECandidate.Solver.Mpt.WitnessDecodeNormalFrame

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Completed node allocations are disjoint from this still-active
branch region. Registering that branch later consumes its own exclusion. -/
def Graph.Excludes {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (pointer : BitVec 64) (size : Nat) : Prop :=
  ∀ node,graph.valid node → node≠0#64 → node.toNat+nodeBytes (wordAt memory node)≤pointer.toNat ∨ pointer.toNat+size≤node.toNat

theorem Graph.excluded_query {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (pointer : BitVec 64) (size : Nat) (excludes : graph.Excludes pointer size)
    (node : BitVec 64) (offset : Nat) (member : graph.valid node) (active : node≠0#64)
    (inside : offset<nodeBytes (wordAt memory node)) :
    (byteAddress node offset).toNat<pointer.toNat ∨ pointer.toNat+size≤(byteAddress node offset).toNat := by
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  have separate:=excludes node member active
  rw [byteAddress_toNat node offset (by have bound:=arena.upper; omega)]
  omega

theorem Graph.excluded_footprint {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (pointer : BitVec 64) (size : Nat) (excludes : graph.Excludes pointer size)
    (query : BitVec 64) (required : graph.Footprint query) : query.toNat<pointer.toNat ∨ pointer.toNat+size≤query.toNat := by
  obtain ⟨node,offset,member,active,inside,notCache,equal⟩:=required.location graph query
  rw [equal]
  exact graph.excluded_query lower upper regions pointer size excludes node offset member active inside

theorem Graph.excluded_value {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (pointer : BitVec 64) (size : Nat) (excludes : graph.Excludes pointer size)
    (query : BitVec 64) (required : ValueFootprint graph query) : query.toNat<pointer.toNat ∨ pointer.toNat+size≤query.toNat := by
  obtain ⟨node,offset,member,active,inside,notCache,equal⟩:=required.location graph query
  rw [equal]
  exact graph.excluded_query lower upper regions pointer size excludes node offset member active inside

/-- Reconstruct the same current registry from real field agreement.
This retains values and disjoint allocation geometry along with structure. -/
theorem Graph.after_agreement (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (domain : target.memaddrs=source.memaddrs)
    (agree : ∀ query,graph.Footprint query → target.memory query=source.memory query)
    (valueAgree : ∀ query,ValueFootprint graph query → target.memory query=source.memory query) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧ Nonempty (Values next limit property) := by
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt target.memory node=wordAt source.memory node := by
    intro node member active
    unfold wordAt
    rw [agree node (.header node member active)]
  let next:=Graph.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph domain agree
  have validEq : next.valid=graph.valid := rfl
  exact ⟨next,validEq,regions.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next lower upper validEq tags,
    disjoint.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next validEq tags,
    ⟨Values.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next limit values validEq domain tags valueAgree⟩⟩

/-- Genuine decode/resolve old-storage frames retain the entire already
completed registry below the actual incoming heap. -/
theorem Graph.after_normal_frame (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (heap cursor scratchLimit : BitVec 64) (above : cursor.toNat≤lower) (before : upper≤heap.toNat)
    (frame : WitnessDecode.NormalFrame source target heap cursor scratchLimit) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧ Nonempty (Values next limit property) := by
  exact graph.after_agreement source target limit lower upper property values regions disjoint frame.domain
    (by intro query required; have bounds:=graph.footprint_bounds lower upper regions query required; exact frame.memory query (by omega) (by omega))
    (by intro query required; have bounds:=graph.value_bounds lower upper regions query required; exact frame.memory query (by omega) (by omega))

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.excluded_footprint
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.excluded_value
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_normal_frame
