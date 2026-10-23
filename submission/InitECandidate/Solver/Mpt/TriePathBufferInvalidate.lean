import InitECandidate.Solver.Mpt.TriePathBuffer
import InitECandidate.Solver.Mpt.TriePathBytesInvalidate

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Cache invalidation preserves an independent current query buffer,
including its protection from every registered mutable node. -/
theorem Graph.PathBuffer.after_invalidate (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (nodeLower nodeUpper lower upper : Nat) (pointer : BitVec 64) (length : Nat)
    (regions : graph.Regions nodeLower nodeUpper) (disjoint : graph.Disjoint) (buffer : graph.PathBuffer source.be lower upper pointer length)
    (owner : BitVec 64) (member : graph.valid owner) (active : owner≠0#64)
    (next : Graph (NodeInvalidate.post source owner).memory source.memaddrs) (validEq : next.valid=graph.valid) :
    next.PathBuffer source.be lower upper pointer length := by
  let post:=NodeInvalidate.post source owner
  have inside (offset : Nat) (small : offset<32) : offset<nodeBytes (wordAt source.memory owner):=by
    have size:=nodeBytes_bounds (wordAt source.memory owner)
    omega
  refine ⟨?_,buffer.bounds,?_⟩
  · apply buffer.span.of_agreement source.memory post.memory source.memaddrs source.memaddrs source.be source.be pointer length rfl rfl
    intro index inBuffer
    exact NodeInvalidate.post_away source owner _
      (buffer.apart index inBuffer owner member active 8 (inside 8 (by decide)))
      (buffer.apart index inBuffer owner member active 16 (inside 16 (by decide)))
      (buffer.apart index inBuffer owner member active 24 (inside 24 (by decide)))
  · intro index inBuffer node nodeMember nodeActive offset within
    have oldMember : graph.valid node:=by rwa [validEq] at nodeMember
    have away (cache : Nat) (positive : 0<cache) (small : cache<32) : node≠owner+BitVec.ofNat 64 cache:=by
      simpa only [byteAddress,BitVec.add_zero] using
        graph.cache_field_away nodeLower nodeUpper regions disjoint owner node 0 cache positive small member active oldMember nodeActive
          (by have size:=nodeBytes_bounds (wordAt source.memory node); omega) (Or.inl rfl)
    have tagEq : wordAt post.memory node=wordAt source.memory node:=by
      unfold wordAt
      rw [NodeInvalidate.post_away source owner node (away 8 (by decide) (by decide)) (away 16 (by decide) (by decide)) (away 24 (by decide) (by decide))]
    rw [tagEq] at within
    exact buffer.apart index inBuffer node oldMember nodeActive offset within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.after_invalidate
