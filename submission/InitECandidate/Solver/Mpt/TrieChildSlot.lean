import InitECandidate.Solver.Mpt.TrieGraphLeafFields

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

inductive ChildSlot (memory : Memory) (owner : BitVec 64) : Nat → Prop where
  | extension (tag : wordAt memory owner=2#64) : ChildSlot memory owner 48
  | branch (notHash : wordAt memory owner≠0#64) (notLeaf : wordAt memory owner≠1#64)
      (notExtension : wordAt memory owner≠2#64) (index : Nat) (inside : index<16) : ChildSlot memory owner (32+index*8)

theorem ChildSlot.bounds (memory : Memory) (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset) :
    32≤offset ∧ offset<160 ∧ offset<nodeBytes (wordAt memory owner) ∧ offset%8=0 := by
  cases slot with
  | extension tag=>rw [tag]; decide
  | branch notHash notLeaf notExtension index inside=>
    simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]
    omega

theorem ChildSlot.not_leaf (memory : Memory) (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset) :
    wordAt memory owner≠1#64 := by
  cases slot with
  | extension tag=>rw [tag]; decide
  | branch notHash notLeaf notExtension index inside=>exact notLeaf

theorem ChildSlot.path_different (memory : Memory) (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset)
    (tag : wordAt memory owner=1#64 ∨ wordAt memory owner=2#64) : offset≠32 ∧ offset≠40 := by
  cases slot with
  | extension extensionTag=>decide
  | branch notHash notLeaf notExtension index inside=>exact (tag.elim notLeaf notExtension).elim

theorem Graph.child_store_header_away {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (node : BitVec 64) (member : graph.valid node) (active : node≠0#64) : node≠owner+BitVec.ofNat 64 offset := by
  have bounds:=slot.bounds memory owner offset
  simpa only [byteAddress,BitVec.add_zero] using graph.field_address_different lower upper regions disjoint owner node 0 offset
    ownerMember ownerActive bounds.2.2.1 member active (by have size:=nodeBytes_bounds (wordAt memory node); omega) (by intro same; omega)

theorem Graph.child_store_path_away {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (node : BitVec 64) (member : graph.valid node) (active : node≠0#64) (tag : wordAt memory node=1#64 ∨ wordAt memory node=2#64) :
    node+32#64≠owner+BitVec.ofNat 64 offset ∧ node+40#64≠owner+BitVec.ofNat 64 offset := by
  have bounds:=slot.bounds memory owner offset
  have different (field : Nat) (wanted : field=32 ∨ field=40) : node=owner → field≠offset:=by
    intro same
    have ownerTag : wordAt memory owner=1#64 ∨ wordAt memory owner=2#64:=by rwa [same] at tag
    have separate:=slot.path_different memory owner offset ownerTag
    omega
  have inside (field : Nat) (wanted : field=32 ∨ field=40) : field<nodeBytes (wordAt memory node):=by
    rcases tag with leaf|extension
    · simpa [leaf,nodeBytes] using (by omega : field<64)
    · simpa [extension,nodeBytes] using (by omega : field<56)
  exact ⟨graph.field_address_different lower upper regions disjoint owner node 32 offset ownerMember ownerActive bounds.2.2.1 member active
      (inside 32 (Or.inl rfl)) (different 32 (Or.inl rfl)),
    graph.field_address_different lower upper regions disjoint owner node 40 offset ownerMember ownerActive bounds.2.2.1 member active
      (inside 40 (Or.inr rfl)) (different 40 (Or.inr rfl))⟩

theorem Graph.child_store_value_away {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (query : BitVec 64) (required : ValueFootprint graph query) : query≠owner+BitVec.ofNat 64 offset := by
  have bounds:=slot.bounds memory owner offset
  cases required with
  | leafPointer node member active tag=>
    exact graph.field_address_different lower upper regions disjoint owner node 48 offset ownerMember ownerActive bounds.2.2.1
      member active (by rw [tag]; decide) (by intro same; exact ((slot.not_leaf memory owner offset) (by rw [←same]; exact tag)).elim)
  | leafLength node member active tag=>
    exact graph.field_address_different lower upper regions disjoint owner node 56 offset ownerMember ownerActive bounds.2.2.1
      member active (by rw [tag]; decide) (by intro same; exact ((slot.not_leaf memory owner offset) (by rw [←same]; exact tag)).elim)
  | branchPointer node member active notHash notLeaf notExtension=>
    exact graph.field_address_different lower upper regions disjoint owner node 160 offset ownerMember ownerActive bounds.2.2.1
      member active (by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide) (by intro same; omega)
  | branchLength node member active notHash notLeaf notExtension=>
    exact graph.field_address_different lower upper regions disjoint owner node 168 offset ownerMember ownerActive bounds.2.2.1
      member active (by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide) (by intro same; omega)

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ChildSlot.bounds
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ChildSlot.not_leaf
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ChildSlot.path_different
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.child_store_header_away
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.child_store_path_away
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.child_store_value_away
