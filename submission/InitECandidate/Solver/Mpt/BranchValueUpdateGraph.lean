import InitECandidate.Solver.Mpt.TrieGraphBranchFields
import InitECandidate.Solver.Mpt.BranchValueUpdateProgram
import InitECandidate.Solver.Mpt.TrieGraphPathBytes

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- The real two branch-value stores preserve structure, every other
value and all path buffers, while installing the current bounded payload. -/
theorem Graph.after_branch_value_update (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (owner pointer size : BitVec 64) (graph : Graph source.memory source.memaddrs)
    (limit lower upper pathLower pathUpper : Nat) (property : BitVec 64 → BitVec 64 → Prop) (values : Values graph limit property)
    (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower pathUpper) (separated : graph.PathSeparated)
    (member : graph.valid owner) (active : owner≠0#64)
    (notHash : wordAt source.memory owner≠0#64) (notLeaf : wordAt source.memory owner≠1#64) (notExtension : wordAt source.memory owner≠2#64)
    (payload : Payload source.memaddrs pointer size limit) (extra : property pointer size) :
    let post:=BranchValueUpdate.post source owner pointer size
    ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower pathUpper ∧ next.PathSeparated := by
  let post:=BranchValueUpdate.post source owner pointer size
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have separate:=graph.branch_value_away lower upper regions disjoint owner query member active notHash notLeaf notExtension required
    exact BranchValueUpdate.post_away source owner pointer size query separate.1 separate.2
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node:=by
    intro node nodeMember nodeActive
    unfold wordAt
    rw [agree node (.header node nodeMember nodeActive)]
  let next:=Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph rfl agree
  have validEq : next.valid=graph.valid:=rfl
  have ownerInside (field : Nat) (which : field=160 ∨ field=168) : field<nodeBytes (wordAt source.memory owner):=by
    simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]
    omega
  have otherFields (node : BitVec 64) (nodeMember : graph.valid node) (nodeActive : node≠0#64)
      (different : node≠owner) (offset : Nat) (inside : offset<nodeBytes (wordAt source.memory node)) :
      post.memory (byteAddress node offset)=source.memory (byteAddress node offset):=by
    apply BranchValueUpdate.post_away
    · exact graph.field_address_different lower upper regions disjoint owner node offset 160 member active (ownerInside 160 (Or.inl rfl))
        nodeMember nodeActive inside (fun same=>(different same).elim)
    · exact graph.field_address_different lower upper regions disjoint owner node offset 168 member active (ownerInside 168 (Or.inr rfl))
        nodeMember nodeActive inside (fun same=>(different same).elim)
  have nextValues : Values next limit property:=by
    constructor
    · intro node nodeMember nodeActive tag
      have oldMember : graph.valid node:=nodeMember
      have oldTag : wordAt source.memory node=1#64:=by rwa [tags node oldMember nodeActive] at tag
      have different : node≠owner:=by intro same; exact notLeaf (by rw [←same]; exact oldTag)
      exact ValueView.of_agreement source.memory post.memory source.memaddrs post.memaddrs node 48#64 56#64 limit
        (values.leaf node oldMember nodeActive oldTag) rfl
        (otherFields node oldMember nodeActive different 48 (by rw [oldTag]; decide))
        (otherFields node oldMember nodeActive different 56 (by rw [oldTag]; decide))
    · intro node nodeMember nodeActive nodeNotHash nodeNotLeaf nodeNotExtension
      have oldMember : graph.valid node:=nodeMember
      rw [tags node oldMember nodeActive] at nodeNotHash nodeNotLeaf nodeNotExtension
      by_cases same : node=owner
      · subst node
        let old:=values.branch owner member active notHash notLeaf notExtension
        have cells:=BranchValueUpdate.post_cells source owner pointer size
        exact {
          pointer:=pointer
          length:=size
          pointerMapped:=old.pointerMapped
          pointerStored:=cells.1
          lengthMapped:=old.lengthMapped
          lengthStored:=cells.2
          payload:=payload
          extra:=extra }
      · have inside (offset : Nat) (small : offset<176) : offset<nodeBytes (wordAt source.memory node):=by
          simpa only [nodeBytes,if_neg nodeNotHash,if_neg nodeNotLeaf,if_neg nodeNotExtension] using small
        exact ValueView.of_agreement source.memory post.memory source.memaddrs post.memaddrs node 160#64 168#64 limit
          (values.branch node oldMember nodeActive nodeNotHash nodeNotLeaf nodeNotExtension) rfl
          (otherFields node oldMember nodeActive same 160 (inside 160 (by decide)))
          (otherFields node oldMember nodeActive same 168 (inside 168 (by decide)))
  have byteWords : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node nodeMember nodeActive tag index inside
    exact BranchValueUpdate.post_away source owner pointer size _
      (separated node nodeMember nodeActive tag index inside owner member active 160 (ownerInside 160 (Or.inl rfl)))
      (separated node nodeMember nodeActive tag index inside owner member active 168 (ownerInside 168 (Or.inr rfl)))
  exact ⟨next,validEq,regions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next lower upper validEq tags,
    disjoint.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq tags,⟨nextValues⟩,
    paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next validEq rfl rfl agree byteWords,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower pathUpper validEq agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next validEq agree⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_branch_value_update
