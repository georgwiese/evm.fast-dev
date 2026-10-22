import InitECandidate.Solver.Mpt.TrieGraphLeafFields
import InitECandidate.Solver.Mpt.LeafUpdateProgram

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Replacing an existing leaf's payload retains its real closed graph,
allocation geometry, and all other leaf and branch values. The new payload
must itself satisfy the current caller's physical value contract. -/
theorem Graph.after_leaf_update (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner pointer size : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (limit lower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (member : graph.valid owner) (active : owner≠0#64) (leaf : wordAt source.memory owner=1#64)
    (payload : Payload source.memaddrs pointer size limit) (extra : property pointer size) :
    let post:=InsertLeaf.post source owner pointer size
    ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) := by
  let post:=InsertLeaf.post source owner pointer size
  have domainEq : post.memaddrs=source.memaddrs:=rfl
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have separate:=graph.leaf_value_away lower upper regions disjoint owner query member active leaf required
    exact InsertLeaf.post_away source owner pointer size query separate.1 separate.2
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node:=by
    intro node nodeMember nodeActive
    unfold wordAt
    rw [agree node (.header node nodeMember nodeActive)]
  let next:=Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph domainEq agree
  have validEq : next.valid=graph.valid:=rfl
  have otherFields (node : BitVec 64) (nodeMember : graph.valid node) (nodeActive : node≠0#64)
      (different : node≠owner) (offset : Nat) (inside : offset<nodeBytes (wordAt source.memory node)) :
      post.memory (byteAddress node offset)=source.memory (byteAddress node offset):=by
    apply InsertLeaf.post_away
    · exact graph.field_address_different lower upper regions disjoint owner node offset 48 member active
        (by rw [leaf]; decide) nodeMember nodeActive inside (fun same=>(different same).elim)
    · exact graph.field_address_different lower upper regions disjoint owner node offset 56 member active
        (by rw [leaf]; decide) nodeMember nodeActive inside (fun same=>(different same).elim)
  have nextValues : Values next limit property:=by
    constructor
    · intro node nodeMember nodeActive tag
      have oldMember : graph.valid node:=nodeMember
      have oldTag : wordAt source.memory node=1#64:=by rwa [tags node oldMember nodeActive] at tag
      by_cases same : node=owner
      · subst node
        let old:=values.leaf owner member active leaf
        have cells:=InsertLeaf.post_cells source owner pointer size
        exact {
          pointer:=pointer
          length:=size
          pointerMapped:=old.pointerMapped
          pointerStored:=cells.1
          lengthMapped:=old.lengthMapped
          lengthStored:=cells.2
          payload:=payload
          extra:=extra }
      · exact ValueView.of_agreement source.memory post.memory source.memaddrs post.memaddrs node 48#64 56#64 limit
          (values.leaf node oldMember nodeActive oldTag) domainEq
          (otherFields node oldMember nodeActive same 48 (by rw [oldTag]; decide))
          (otherFields node oldMember nodeActive same 56 (by rw [oldTag]; decide))
    · intro node nodeMember nodeActive notHash notLeaf notExtension
      have oldMember : graph.valid node:=nodeMember
      rw [tags node oldMember nodeActive] at notHash notLeaf notExtension
      have different : node≠owner:=by intro same; exact notLeaf (by rw [same]; exact leaf)
      have inside (offset : Nat) (small : offset<176) : offset<nodeBytes (wordAt source.memory node):=by
        simpa only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension] using small
      exact ValueView.of_agreement source.memory post.memory source.memaddrs post.memaddrs node 160#64 168#64 limit
        (values.branch node oldMember nodeActive notHash notLeaf notExtension) domainEq
        (otherFields node oldMember nodeActive different 160 (inside 160 (by decide)))
        (otherFields node oldMember nodeActive different 168 (inside 168 (by decide)))
  exact ⟨next,validEq,regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next lower upper validEq tags,
    disjoint.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq tags,⟨nextValues⟩⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_leaf_update
