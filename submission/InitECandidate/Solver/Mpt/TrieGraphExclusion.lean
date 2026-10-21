import InitECandidate.Solver.Mpt.TrieGraphStorageFrame

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack GasBudget WitnessRadix

theorem Graph.Excludes.empty (memory : Memory) (domain : BitVec 64 → Prop) (pointer : BitVec 64) (size : Nat) :
    (Graph.empty memory domain).Excludes pointer size := by
  intro node member active; exact (active member).elim

/-- Preserve the exclusion of a still-active branch when the registry
keeps its old nodes and may add the newly completed result after it. -/
theorem Graph.Excludes.after_extension (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (pointer result : BitVec 64) (size : Nat)
    (excluded : graph.Excludes pointer size)
    (members : ∀ node,next.valid node → graph.valid node ∨ node=result)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node)
    (resultAfter : result≠0#64 → pointer.toNat+size≤result.toNat) : next.Excludes pointer size := by
  intro node member active
  rcases members node member with prior|fresh
  · rw [tags node prior active]
    exact excluded node prior active
  · subst node
    exact Or.inr (resultAfter active)

theorem Graph.Excludes.of_agreement (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (pointer : BitVec 64) (size : Nat)
    (excluded : graph.Excludes pointer size) (validEq : next.valid=graph.valid)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node) : next.Excludes pointer size := by
  intro node member active
  have prior : graph.valid node := by rwa [validEq] at member
  rw [tags node prior active]
  exact excluded node prior active

theorem Graph.Excludes.register (memory : Memory) (domain : BitVec 64 → Prop)
    (graph : Graph memory domain) (node pointer : BitVec 64) (size : Nat) (data : Registration graph node)
    (excluded : graph.Excludes pointer size)
    (separate : node≠0#64 → node.toNat+nodeBytes (wordAt memory node)≤pointer.toNat ∨ pointer.toNat+size≤node.toNat) :
    (graph.register node data).Excludes pointer size := by
  intro current member active
  rcases member with prior|fresh
  · exact excluded current prior active
  · subst current; exact separate active

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Excludes.after_extension
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Excludes.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Excludes.register
