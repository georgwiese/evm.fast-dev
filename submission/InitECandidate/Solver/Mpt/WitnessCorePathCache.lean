import InitECandidate.Solver.Mpt.WitnessCorePathFrame

namespace InitECandidate.Solver.Mpt.WitnessCore.Stack
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real conditional child HASH24 write preserves completed and
pending path bytes. Pending extension buffers are protected by their
separation from every registered mutable node, including this child. -/
theorem ActiveRegistry.PathModel.cache (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db child hash : BitVec 64) (cfg : Configuration)
    (registry : ActiveRegistry source frontier db cfg)
    (next : ActiveRegistry (returnCacheState source child hash) frontier db cfg)
    (paths : registry.PathModel) (validEq : next.nodes.graph.valid=registry.nodes.graph.valid)
    (member : registry.nodes.graph.valid child) : next.PathModel := by
  let post:=returnCacheState source child hash
  have domain : post.memaddrs=source.memaddrs:=by unfold post returnCacheState; split <;> rfl
  have endian : post.be=source.be:=by unfold post returnCacheState; split <;> rfl
  by_cases zero : child=0#64
  · have memory : post.memory=source.memory:=by simp [post,returnCacheState,zero]
    exact paths.of_fields source post frontier db cfg registry next validEq memory domain endian
  · have agree : ∀ query,registry.nodes.graph.Footprint query → post.memory query=source.memory query:=by
      intro query required
      obtain ⟨node,offset,nodeMember,active,inside,notCache,equal⟩:=required.location registry.nodes.graph query
      exact return_cache_memory source child hash query (by
        rw [equal]
        exact registry.nodes.graph.cache_away frontier cfg.heap.toNat registry.nodes.regions registry.nodes.disjoint child node offset member zero nodeMember active inside notCache)
    have tags (node : BitVec 64) (member : registry.nodes.graph.valid node) (active : node≠0#64) :
        wordAt post.memory node=wordAt source.memory node:=by
      unfold wordAt
      rw [agree node (.header node member active)]
    have nodes:=paths.nodes.cache source frontier cfg.heap db child hash registry.nodes member next.nodes validEq
    refine ⟨nodes,?_,?_,?_,paths.pendingPending⟩
    · intro current inStack
      cases payload : current.data.payload with
      | branch owner slot occupied=>trivial
      | extension pointer length=>
        have bytes:=paths.pending current inStack
        simp only [payload,WitnessRecord.Payload.PathBytes] at bytes
        change TrieWalk.NibbleSpan post.memory post.memaddrs post.be pointer length.toNat ∧ pointer.toNat%8=0
        refine ⟨bytes.1.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be pointer length.toNat domain endian ?_,bytes.2⟩
        intro index inside
        exact return_cache_memory source child hash _ (paths.pendingNode current inStack pointer length payload index inside child member zero 24
          (by have bounds:=TrieWalk.nodeBytes_bounds (wordAt source.memory child); omega))
    · intro node nodeMember active tag index inside current inStack owner slot occupied payload offset offsetInside
      have oldMember : registry.nodes.graph.valid node:=by rwa [validEq] at nodeMember
      have oldTag : wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64:=by rwa [tags node oldMember active] at tag
      have fields:=registry.nodes.graph.path_word_agreement post.memory agree node oldMember active oldTag
      rw [fields.2] at inside
      rw [fields.1]
      exact paths.nodePending node oldMember active oldTag index inside current inStack owner slot occupied payload offset offsetInside
    · intro current inStack pointer length payload index inside owner ownerMember active offset offsetInside
      have oldMember : registry.nodes.graph.valid owner:=by rwa [validEq] at ownerMember
      rw [tags owner oldMember active] at offsetInside
      exact paths.pendingNode current inStack pointer length payload index inside owner oldMember active offset offsetInside

end InitECandidate.Solver.Mpt.WitnessCore.Stack

#print axioms InitECandidate.Solver.Mpt.WitnessCore.Stack.ActiveRegistry.PathModel.cache
