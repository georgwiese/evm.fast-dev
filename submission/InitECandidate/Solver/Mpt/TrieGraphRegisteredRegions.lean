import InitECandidate.Solver.Mpt.TrieGraphRegions
import InitECandidate.Solver.Mpt.TrieGraphRegister

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.Regions.empty (memory : Memory) (domain : BitVec 64  →  Prop) (lower upper : Nat) :
    (Graph.empty memory domain).Regions lower upper := by
  intro node member active; exact (active member).elim

theorem Graph.Disjoint.empty (memory : Memory) (domain : BitVec 64  →  Prop) : (Graph.empty memory domain).Disjoint := by
  intro node member active; exact (active member).elim

theorem Graph.Regions.weaken {memory : Memory} {domain : BitVec 64  →  Prop}
    (graph : Graph memory domain) (lower upper smaller larger : Nat) (regions : graph.Regions lower upper)
    (first : smaller≤lower) (last : upper≤larger) : graph.Regions smaller larger := by
  intro node member active
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  exact ⟨Nat.le_trans first floor,arena,aligned,Nat.le_trans before last⟩

/-- Real registration adds only one actual node allocation to the old
registry. All physical facts for old nodes remain at the same current memory. -/
theorem Graph.Regions.register {memory : Memory} {domain : BitVec 64  →  Prop}
    (graph : Graph memory domain) (node : BitVec 64) (data : Registration graph node) (lower upper : Nat)
    (regions : graph.Regions lower upper) (floor : lower≤node.toNat)
    (arena : AllocatedBytes.Arena node (nodeBytes (wordAt memory node))) (aligned : node.toNat%8=0)
    (before : node.toNat+nodeBytes (wordAt memory node)≤upper) : (graph.register node data).Regions lower upper := by
  intro current member active
  rcases member with old|fresh
  · exact regions current old active
  · subst current; exact ⟨floor,arena,aligned,before⟩

theorem Graph.Disjoint.register {memory : Memory} {domain : BitVec 64  →  Prop}
    (graph : Graph memory domain) (node : BitVec 64) (data : Registration graph node) (disjoint : graph.Disjoint)
    (separate : ∀ old,graph.valid old → old≠0#64 → old≠node → 
      node.toNat+nodeBytes (wordAt memory node)≤old.toNat ∨ old.toNat+nodeBytes (wordAt memory old)≤node.toNat) :
    (graph.register node data).Disjoint := by
  intro first firstMember firstActive second secondMember secondActive different
  rcases firstMember with firstOld|firstNew
  · rcases secondMember with secondOld|secondNew
    · exact disjoint first firstOld firstActive second secondOld secondActive different
    · subst second; exact (separate first firstOld firstActive different).symm
  · subst first
    rcases secondMember with secondOld|secondNew
    · exact separate second secondOld secondActive (Ne.symm different)
    · exact (different secondNew.symm).elim

/-- Preserve allocation/lifetime geometry through agreement on node tags
and the same registered membership; arbitrary unrelated memory may change. -/
theorem Graph.Regions.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64  →  Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (lower upper : Nat) (regions : graph.Regions lower upper)
    (validEq : next.valid=graph.valid)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node) : next.Regions lower upper := by
  intro node member active
  have oldMember : graph.valid node := by rwa [validEq] at member
  change lower≤node.toNat ∧ AllocatedBytes.Arena node (nodeBytes (wordAt memory' node)) ∧
    node.toNat%8=0 ∧ node.toNat+nodeBytes (wordAt memory' node)≤upper
  rw [tags node oldMember active]
  exact regions node oldMember active

theorem Graph.Disjoint.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64  →  Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (disjoint : graph.Disjoint)
    (validEq : next.valid=graph.valid)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node) : next.Disjoint := by
  intro first firstMember firstActive second secondMember secondActive different
  have firstOld : graph.valid first := by rwa [validEq] at firstMember
  have secondOld : graph.valid second := by rwa [validEq] at secondMember
  change first.toNat+nodeBytes (wordAt memory' first)≤second.toNat ∨ second.toNat+nodeBytes (wordAt memory' second)≤first.toNat
  rw [tags first firstOld firstActive,tags second secondOld secondActive]
  exact disjoint first firstOld firstActive second secondOld secondActive different

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Regions.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Disjoint.register
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Regions.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Disjoint.of_agreement
