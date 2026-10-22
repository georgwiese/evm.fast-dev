import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Two registered node fields are separate whenever their allocations
are disjoint, or they occupy distinct offsets of the same actual node. -/
theorem Graph.field_address_different {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner node : BitVec 64) (offset ownerOffset : Nat)
    (ownerMember : graph.valid owner) (ownerActive : owner≠0#64) (ownerInside : ownerOffset<nodeBytes (wordAt memory owner))
    (member : graph.valid node) (active : node≠0#64) (inside : offset<nodeBytes (wordAt memory node))
    (different : node=owner → offset≠ownerOffset) : byteAddress node offset≠owner+BitVec.ofNat 64 ownerOffset := by
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  obtain ⟨ownerFloor,ownerArena,ownerAligned,ownerBefore⟩:=regions owner ownerMember ownerActive
  have size:=nodeBytes_bounds (wordAt memory node)
  have ownerSize:=nodeBytes_bounds (wordAt memory owner)
  intro equal
  by_cases same : node=owner
  · have offsets : BitVec.ofNat 64 offset=BitVec.ofNat 64 ownerOffset:=by
      rw [same] at equal
      exact (BitVec.add_right_inj owner).mp equal
    have numeric:=congrArg BitVec.toNat offsets
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at numeric
    exact different same numeric
  · have separate:=disjoint node member active owner ownerMember ownerActive same
    have firstNumber : (byteAddress node offset).toNat=node.toNat+offset:=byteAddress_toNat node offset (by have bound:=arena.upper; omega)
    have ownerNumber : (owner+BitVec.ofNat 64 ownerOffset).toNat=owner.toNat+ownerOffset:=byteAddress_toNat owner ownerOffset (by have bound:=ownerArena.upper; omega)
    have numeric:=congrArg BitVec.toNat equal
    rw [firstNumber,ownerNumber] at numeric
    omega

/-- Structural reads never include a current leaf's two mutable value
fields. The tag excludes extension/branch interpretations of that owner. -/
theorem Graph.Footprint.leaf_location {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (owner query : BitVec 64) (leaf : wordAt memory owner=1#64) (required : graph.Footprint query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧ query=byteAddress node offset ∧
      (node=owner → offset≠48 ∧ offset≠56) := by
  cases required with
  | header node member active=>exact ⟨query,0,member,active,by have size:=nodeBytes_bounds (wordAt memory query); omega,by simp [byteAddress],by intro same; exact ⟨by decide,by decide⟩⟩
  | pointer node member active tag=>
    refine ⟨node,32,member,active,?_,rfl,by intro same; exact ⟨by decide,by decide⟩⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | size node member active tag=>
    refine ⟨node,40,member,active,?_,rfl,by intro same; exact ⟨by decide,by decide⟩⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | extension node member active tag=>
    refine ⟨node,48,member,active,by rw [tag]; decide,rfl,?_⟩
    intro same
    rw [same,leaf] at tag
    cases tag
  | branch node member active notHash notLeaf notExtension index inside=>
    refine ⟨node,32+index*8,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; omega,?_,?_⟩
    · rw [byteAddress,BitVec.ofNat_add,←BitVec.add_assoc]
    · intro same
      exact (notLeaf (by rw [same]; exact leaf)).elim

theorem Graph.leaf_value_away {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner query : BitVec 64) (member : graph.valid owner) (active : owner≠0#64) (leaf : wordAt memory owner=1#64)
    (required : graph.Footprint query) : query≠owner+48#64 ∧ query≠owner+56#64 := by
  obtain ⟨node,offset,nodeMember,nodeActive,inside,equal,different⟩:=required.leaf_location graph owner query leaf
  rw [equal]
  exact ⟨graph.field_address_different lower upper regions disjoint owner node offset 48 member active (by rw [leaf]; decide)
      nodeMember nodeActive inside (fun same=>(different same).1),
    graph.field_address_different lower upper regions disjoint owner node offset 56 member active (by rw [leaf]; decide)
      nodeMember nodeActive inside (fun same=>(different same).2)⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.field_address_different
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Footprint.leaf_location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.leaf_value_away
