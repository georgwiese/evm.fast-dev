import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.Mpt.TrieGraphInvalidateFrame
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The three genuine cache clears retain saved parent descriptors. -/
theorem Graph.PathFields.of_invalidate (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (member : graph.valid owner) (active : owner≠0#64) : graph.PathFields (NodeInvalidate.post source owner).memory := by
  apply Graph.PathFields.of_agreement
  intro query required
  obtain ⟨node,offset,nodeMember,nodeActive,inside,data,equal⟩:=required.data_location graph query
  apply NodeInvalidate.post_away source owner query
  all_goals
    rw [equal]
    exact graph.cache_field_away lower upper regions disjoint owner node offset _ (by decide) (by decide)
      member active nodeMember nodeActive inside data

/-- Clearing the terminal branch value, or replacing it, retains the
tag and complete path descriptor of every saved ancestor. -/
theorem Graph.PathFields.of_branch_value (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner pointer size : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (member : graph.valid owner) (active : owner≠0#64)
    (notHash : wordAt source.memory owner≠0#64) (notLeaf : wordAt source.memory owner≠1#64) (notExtension : wordAt source.memory owner≠2#64) :
    graph.PathFields (BranchValueUpdate.post source owner pointer size).memory := by
  apply Graph.PathFields.of_agreement
  intro query required
  have separate:=graph.branch_value_away lower upper regions disjoint owner query member active notHash notLeaf notExtension required
  exact BranchValueUpdate.post_away source owner pointer size query separate.1 separate.2

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.of_invalidate
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.of_branch_value
