import InitECandidate.Solver.Mpt.NodeInvalidatePathCall

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real cache stores preserve the older allocation prefix and every
registered node tag. These are derived from actual node geometry. -/
theorem Graph.invalidate_memory_frames (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner : BitVec 64) (graph : Graph source.memory source.memaddrs) (lower upper : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (member : graph.valid owner) (active : owner≠0#64) :
    (∀ query : BitVec 64,query.toNat<lower → (NodeInvalidate.post source owner).memory query=source.memory query) ∧
      ∀ node,graph.valid node → node≠0#64 → wordAt (NodeInvalidate.post source owner).memory node=wordAt source.memory node := by
  constructor
  · intro query before
    have bounds:=regions owner member active
    have away (offset : Nat) (inside : offset<32) : query≠byteAddress owner offset:=by
      intro equal
      have number:=congrArg BitVec.toNat equal
      rw [byteAddress_toNat owner offset (by have last:=bounds.2.1.upper; have size:=nodeBytes_bounds (wordAt source.memory owner); omega)] at number
      omega
    exact NodeInvalidate.post_away source owner query (away 8 (by decide)) (away 16 (by decide)) (away 24 (by decide))
  · intro node live nonzero
    have away (offset : Nat) (positive : 0<offset) (small : offset<32) : node≠owner+BitVec.ofNat 64 offset:=by
      simpa only [byteAddress,BitVec.add_zero] using graph.cache_field_away lower upper regions disjoint owner node 0 offset positive small member active live nonzero
        (by have size:=nodeBytes_bounds (wordAt source.memory node); omega) (Or.inl rfl)
    unfold wordAt
    rw [NodeInvalidate.post_away source owner node (away 8 (by decide) (by decide)) (away 16 (by decide) (by decide)) (away 24 (by decide) (by decide))]

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.invalidate_memory_frames
