import InitECandidate.Solver.Mpt.TrieGraphCacheOffsets
import InitECandidate.Solver.Mpt.TrieProtectedWord

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Original serialization/cache stores at offsets8,16and24 change no
node tag, child/value field or full path byte. They preserve separated
caller words and the complete same-registry physical trie. -/
theorem Graph.after_metadata_store (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner value : BitVec 64) (cache : Nat) (positive : 0<cache) (small : cache<32)
    (graph : Graph source.memory source.memaddrs) (limit lower pathLower upper : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (member : graph.valid owner) (active : owner≠0#64) :
    let post:={source with memory:=StoreWord.put source.memory (owner+BitVec.ofNat 64 cache) value}
    graph.PathFields post.memory ∧ ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated ∧
      (∀ query,graph.ProtectedWord query→post.memory query=source.memory query ∧ next.ProtectedWord query) := by
  let post:={source with memory:=StoreWord.put source.memory (owner+BitVec.ofNat 64 cache) value}
  have agree : ∀ query,graph.Footprint query→post.memory query=source.memory query:=by
    intro query required
    obtain ⟨node,offset,live,nodeActive,inside,data,equal⟩:=required.data_location graph query
    exact if_neg (by rw [equal]; exact graph.cache_field_away lower upper regions disjoint owner node offset cache positive small member active live nodeActive inside data)
  have valueAgree : ∀ query,ValueFootprint graph query→post.memory query=source.memory query:=by
    intro query required
    obtain ⟨node,offset,live,nodeActive,inside,data,equal⟩:=required.data_location graph query
    exact if_neg (by rw [equal]; exact graph.cache_field_away lower upper regions disjoint owner node offset cache positive small member active live nodeActive inside data)
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_agreement source post limit lower upper property values regions disjoint rfl agree valueAgree
  have bytes : ∀ node,graph.valid node→node≠0#64→(wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)→
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
          source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node live nodeActive tag index inside
    apply if_neg
    exact separated node live nodeActive tag index inside owner member active cache (by have size:=nodeBytes_bounds (wordAt source.memory owner); omega)
  have fields:=Graph.PathFields.of_agreement graph post.memory agree
  refine ⟨fields,next,same,nextRegions,nextDisjoint,nextValues,
    paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next same rfl rfl agree bytes,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower upper same agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next same agree,?_⟩
  intro query safe
  have away : query≠owner+BitVec.ofNat 64 cache:=safe.nodes owner member active cache (by have size:=nodeBytes_bounds (wordAt source.memory owner); omega)
  exact ⟨if_neg away,safe.of_fields graph next query same fields⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_metadata_store
