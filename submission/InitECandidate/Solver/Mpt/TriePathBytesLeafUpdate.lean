import InitECandidate.Solver.Mpt.TrieGraphPathBytes
import InitECandidate.Solver.Mpt.TrieGraphLeafFields
import InitECandidate.Solver.Mpt.LeafUpdateProgram

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The two original leaf-value stores retain the full actual path-byte
model, positive extensions and buffer/node separation. These facts are
transported to any closed graph with the same real node membership at the
post-state; no future mutation model is supplied. -/
theorem Graph.leaf_update_path_models (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner pointer size : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (lower upper pathLower pathUpper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid owner) (active : owner≠0#64) (leaf : wordAt source.memory owner=1#64)
    (next : Graph (InsertLeaf.post source owner pointer size).memory (InsertLeaf.post source owner pointer size).memaddrs)
    (validEq : next.valid=graph.valid) :
    next.PathBytes (InsertLeaf.post source owner pointer size).be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  let post:=InsertLeaf.post source owner pointer size
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have apart:=graph.leaf_value_away lower upper regions disjoint owner query member active leaf required
    exact InsertLeaf.post_away source owner pointer size query apart.1 apart.2
  have bytes : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node nodeMember nodeActive tag index inside
    apply InsertLeaf.post_away
    · exact separated node nodeMember nodeActive tag index inside owner member active 48 (by rw [leaf]; decide)
    · exact separated node nodeMember nodeActive tag index inside owner member active 56 (by rw [leaf]; decide)
  exact ⟨paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next validEq rfl rfl agree bytes,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower pathUpper validEq agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq agree⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.leaf_update_path_models
