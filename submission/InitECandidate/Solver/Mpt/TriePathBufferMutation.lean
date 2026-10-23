import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.BranchValueUpdateGraph

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Keep independent split/query buffers when a real fresh constructor
adds one node above them. Only the actual old-word frame and membership
extension are used; the buffers may be unaligned borrowed windows. -/
theorem Graph.PathBuffer.after_fresh_node (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (nodeLower lower : Nat) (heap pointer : BitVec 64) (length : Nat)
    (regions : graph.Regions nodeLower heap.toNat) (buffer : graph.PathBuffer source.be lower heap.toNat pointer length)
    (members : ∀ node,next.valid node → graph.valid node ∨ node=heap)
    (arena : AllocatedBytes.Arena heap (nodeBytes (wordAt target.memory heap)))
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query) :
    next.PathBuffer target.be lower heap.toNat pointer length := by
  have span:=buffer.span.of_before source target pointer length heap.toNat buffer.bounds.2 domain endian memory
  refine ⟨span,buffer.bounds,?_⟩
  intro index inside owner member active offset within
  rcases members owner member with old|fresh
  · have bounds:=regions owner old active
    have tagEq : wordAt target.memory owner=wordAt source.memory owner:=by
      unfold wordAt
      rw [memory owner (by have size:=(nodeBytes_bounds (wordAt source.memory owner)).1; omega)]
    rw [tagEq] at within
    exact buffer.apart index inside owner old active offset within
  · subst owner
    exact span.apart_before target.memory target.memaddrs target.be pointer heap length _ arena buffer.bounds.2 index inside offset within

/-- Original branch-value writes also preserve buffers that have not yet
been installed into any node, such as the other half of a pending split. -/
theorem Graph.PathBuffer.after_branch_value_update (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (nodeLower nodeUpper lower upper : Nat) (pointer : BitVec 64) (length : Nat)
    (regions : graph.Regions nodeLower nodeUpper) (disjoint : graph.Disjoint) (buffer : graph.PathBuffer source.be lower upper pointer length)
    (owner value size : BitVec 64) (member : graph.valid owner) (active : owner≠0#64)
    (notHash : wordAt source.memory owner≠0#64) (notLeaf : wordAt source.memory owner≠1#64) (notExtension : wordAt source.memory owner≠2#64)
    (next : Graph (BranchValueUpdate.post source owner value size).memory source.memaddrs) (validEq : next.valid=graph.valid) :
    next.PathBuffer source.be lower upper pointer length := by
  let post:=BranchValueUpdate.post source owner value size
  have ownerInside (field : Nat) (which : field=160 ∨ field=168) : field<nodeBytes (wordAt source.memory owner):=by
    simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]
    omega
  refine ⟨?_,buffer.bounds,?_⟩
  · apply buffer.span.of_agreement source.memory post.memory source.memaddrs source.memaddrs source.be source.be pointer length rfl rfl
    intro index inside
    exact BranchValueUpdate.post_away source owner value size _
      (buffer.apart index inside owner member active 160 (ownerInside 160 (Or.inl rfl)))
      (buffer.apart index inside owner member active 168 (ownerInside 168 (Or.inr rfl)))
  · intro index inside node nodeMember nodeActive offset within
    have oldMember : graph.valid node:=by rwa [validEq] at nodeMember
    have away:=graph.branch_value_away nodeLower nodeUpper regions disjoint owner node member active notHash notLeaf notExtension (.header node oldMember nodeActive)
    have tagEq : wordAt post.memory node=wordAt source.memory node:=by
      unfold wordAt
      rw [BranchValueUpdate.post_away source owner value size node away.1 away.2]
    rw [tagEq] at within
    exact buffer.apart index inside node oldMember nodeActive offset within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.after_fresh_node
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.after_branch_value_update
