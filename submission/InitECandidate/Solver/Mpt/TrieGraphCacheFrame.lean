import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions
import InitECandidate.Solver.Mpt.WitnessCoreReturnCache

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The actual HASH24 cache update preserves the closed physical graph,
all real value fields and the same disjoint node allocation lifetimes.
Children may be shared; only real allocation overlap is excluded. -/
theorem Graph.after_cache (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner hash : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (limit lower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint) (member : graph.valid owner) :
    let post:=WitnessCore.returnCacheState source owner hash
    ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) := by
  by_cases zero : owner=0#64
  · rw [WitnessCore.returnCacheState,if_pos (Or.inr zero)]
    exact ⟨graph,rfl,regions,disjoint,⟨values⟩⟩
  · let post:=WitnessCore.returnCacheState source owner hash
    have domainEq : post.memaddrs=source.memaddrs := by unfold post WitnessCore.returnCacheState; split <;> rfl
    have agree : ∀ query,graph.Footprint query→post.memory query=source.memory query := by
      intro query required
      obtain ⟨node,offset,nodeMember,active,inside,notCache,equal⟩:=required.location graph query
      exact WitnessCore.return_cache_memory source owner hash query (by
        rw [equal]
        exact graph.cache_away lower upper regions disjoint owner node offset member zero nodeMember active inside notCache)
    have valueAgree : ∀ query,ValueFootprint graph query→post.memory query=source.memory query := by
      intro query required
      obtain ⟨node,offset,nodeMember,active,inside,notCache,equal⟩:=required.location graph query
      exact WitnessCore.return_cache_memory source owner hash query (by
        rw [equal]
        exact graph.cache_away lower upper regions disjoint owner node offset member zero nodeMember active inside notCache)
    have tags : ∀ node,graph.valid node→node≠0#64→wordAt post.memory node=wordAt source.memory node := by
      intro node nodeMember active
      unfold wordAt
      rw [agree node (.header node nodeMember active)]
    let next:=Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph domainEq agree
    have validEq : next.valid=graph.valid := rfl
    exact ⟨next,validEq,regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next lower upper validEq tags,
      disjoint.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq tags,
      ⟨Values.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next limit values validEq domainEq tags valueAgree⟩⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_cache
