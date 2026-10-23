import InitECandidate.Solver.Mpt.TriePathRegisterFresh

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Register a genuinely fresh path node and retain the complete live
graph, bounded values, allocation geometry and full path-byte model. -/
theorem Graph.register_fresh_path {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (be : Bool) (limit nodeLower pathLower upper nextUpper : Nat)
    (property : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (node pointer length : BitVec 64) (data : Registration graph node)
    (tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64)
    (pointerStored : wordAt memory (node+32#64)=pointer) (lengthStored : wordAt memory (node+40#64)=length)
    (positive : wordAt memory node=2#64 → 0<length.toNat)
    (arena : AllocatedBytes.Arena node (nodeBytes (wordAt memory node))) (aligned : node.toNat%8=0)
    (floor : nodeLower≤node.toNat) (fresh : upper≤node.toNat) (before : node.toNat+nodeBytes (wordAt memory node)≤nextUpper)
    (buffer : graph.PathBuffer be pathLower upper pointer length.toNat)
    (leaf : wordAt memory node=1#64 → ValueView memory domain node 48#64 56#64 limit property) :
    (graph.register node data).Regions nodeLower nextUpper ∧ (graph.register node data).Disjoint ∧
      Nonempty (Values (graph.register node data) limit property) ∧ (graph.register node data).PathBytes be ∧
      (graph.register node data).PathRegions pathLower nextUpper ∧ (graph.register node data).PathSeparated := by
  have grows : upper≤nextUpper:=by omega
  obtain ⟨nextPaths,nextPathRegions,nextSeparated⟩:=graph.register_borrowed_paths be pathLower upper nextUpper paths pathRegions separated
    node pointer length data tag pointerStored lengthStored positive arena fresh grows buffer
  have nextRegions:=(regions.weaken graph nodeLower upper nodeLower nextUpper (Nat.le_refl _) grows).register graph node data nodeLower nextUpper floor arena aligned before
  have nextDisjoint:=disjoint.register graph node data (by
    intro old member active different
    exact Or.inr ((regions old member active).2.2.2.trans fresh))
  let nextValues:=Values.register graph node data limit values leaf (by
    intro notHash notLeaf notExtension
    have impossible : False:=tag.elim notLeaf notExtension
    exact impossible.elim)
  exact ⟨nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.register_fresh_path
