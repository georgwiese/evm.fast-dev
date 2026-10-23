import InitECandidate.Solver.Mpt.TrieGraphPathBytes
import InitECandidate.Solver.Mpt.TrieGraphInvalidateFrame

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Original cache invalidation preserves full path bytes, positive
extensions and allocation separation, not just the structural metadata. -/
theorem Graph.invalidate_path_models (source : PanSemStateFiniteExact 64 Guest.HostMemory) (owner : BitVec 64)
    (graph : Graph source.memory source.memaddrs) (lower upper pathLower pathUpper : Nat)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid owner) (active : owner≠0#64)
    (next : Graph (NodeInvalidate.post source owner).memory (NodeInvalidate.post source owner).memaddrs)
    (validEq : next.valid=graph.valid) :
    next.PathBytes (NodeInvalidate.post source owner).be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  let post:=NodeInvalidate.post source owner
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    obtain ⟨node,offset,nodeMember,nodeActive,inside,data,equal⟩:=required.data_location graph query
    apply NodeInvalidate.post_away source owner query
    all_goals
      rw [equal]
      exact graph.cache_field_away lower upper regions disjoint owner node offset _ (by decide) (by decide)
        member active nodeMember nodeActive inside data
  have bytes : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node nodeMember nodeActive tag index inside
    apply NodeInvalidate.post_away
    all_goals
      exact separated node nodeMember nodeActive tag index inside owner member active _ (by have bound:=nodeBytes_bounds (wordAt source.memory owner); omega)
  exact ⟨paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next validEq rfl rfl agree bytes,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower pathUpper validEq agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq agree⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.invalidate_path_models
