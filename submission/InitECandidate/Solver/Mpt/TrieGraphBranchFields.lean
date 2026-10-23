import InitECandidate.Solver.Mpt.TrieGraphLeafFields

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- All structural fields precede a branch's value fields at160/168. -/
theorem Graph.Footprint.small_location {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (query : BitVec 64) (required : graph.Footprint query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧ offset<160 ∧ query=byteAddress node offset := by
  cases required with
  | header node member active=>exact ⟨query,0,member,active,by have size:=nodeBytes_bounds (wordAt memory query); omega,by decide,by simp [byteAddress]⟩
  | pointer node member active tag=>
    refine ⟨node,32,member,active,?_,by decide,rfl⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | size node member active tag=>
    refine ⟨node,40,member,active,?_,by decide,rfl⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | extension node member active tag=>exact ⟨node,48,member,active,by rw [tag]; decide,by decide,rfl⟩
  | branch node member active notHash notLeaf notExtension index inside=>
    refine ⟨node,32+index*8,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; omega,by omega,?_⟩
    rw [byteAddress,BitVec.ofNat_add,←BitVec.add_assoc]

theorem Graph.branch_value_away {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner query : BitVec 64) (member : graph.valid owner) (active : owner≠0#64)
    (notHash : wordAt memory owner≠0#64) (notLeaf : wordAt memory owner≠1#64) (notExtension : wordAt memory owner≠2#64)
    (required : graph.Footprint query) : query≠owner+160#64 ∧ query≠owner+168#64 := by
  obtain ⟨node,offset,nodeMember,nodeActive,inside,small,equal⟩:=required.small_location graph query
  have ownerInside (field : Nat) (which : field=160 ∨ field=168) : field<nodeBytes (wordAt memory owner):=by
    simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]
    omega
  rw [equal]
  exact ⟨graph.field_address_different lower upper regions disjoint owner node offset 160 member active (ownerInside 160 (Or.inl rfl))
      nodeMember nodeActive inside (by intro same; omega),
    graph.field_address_different lower upper regions disjoint owner node offset 168 member active (ownerInside 168 (Or.inr rfl))
      nodeMember nodeActive inside (by intro same; omega)⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Footprint.small_location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.branch_value_away
