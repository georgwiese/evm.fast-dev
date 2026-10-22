import InitECandidate.Solver.Mpt.TrieGraphRegisteredRegions

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.Footprint.data_location {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query : BitVec 64) (required : graph.Footprint query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧
      (offset=0 ∨ 32≤offset) ∧ query=byteAddress node offset := by
  cases required with
  | header node member active=>exact ⟨query,0,member,active,by have size:=nodeBytes_bounds (wordAt memory query); omega,Or.inl rfl,by simp [byteAddress]⟩
  | pointer node member active tag=>
    refine ⟨node,32,member,active,?_,Or.inr (by decide),rfl⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | size node member active tag=>
    refine ⟨node,40,member,active,?_,Or.inr (by decide),rfl⟩
    rcases tag with tag|tag <;> rw [tag] <;> decide
  | extension node member active tag=>exact ⟨node,48,member,active,by rw [tag]; decide,Or.inr (by decide),rfl⟩
  | branch node member active notHash notLeaf notExtension index inside=>
    refine ⟨node,32+index*8,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; omega,Or.inr (by omega),?_⟩
    rw [byteAddress,BitVec.ofNat_add,←BitVec.add_assoc]

theorem ValueFootprint.data_location {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query : BitVec 64) (required : ValueFootprint graph query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧
      (offset=0 ∨ 32≤offset) ∧ query=byteAddress node offset := by
  cases required with
  | leafPointer node member active tag=>exact ⟨node,48,member,active,by rw [tag]; decide,Or.inr (by decide),rfl⟩
  | leafLength node member active tag=>exact ⟨node,56,member,active,by rw [tag]; decide,Or.inr (by decide),rfl⟩
  | branchPointer node member active notHash notLeaf notExtension=>
    exact ⟨node,160,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide,Or.inr (by decide),rfl⟩
  | branchLength node member active notHash notLeaf notExtension=>
    exact ⟨node,168,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide,Or.inr (by decide),rfl⟩

/-- Every real structural/value field is separate from each metadata
cache word, within its own node and every other disjoint node allocation. -/
theorem Graph.cache_field_away {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner node : BitVec 64) (offset cache : Nat) (cachePositive : 0<cache) (cacheSmall : cache<32)
    (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (member : graph.valid node) (active : node≠0#64) (inside : offset<nodeBytes (wordAt memory node))
    (data : offset=0 ∨ 32≤offset) : byteAddress node offset≠owner+BitVec.ofNat 64 cache := by
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  obtain ⟨ownerFloor,ownerArena,ownerAligned,ownerBefore⟩:=regions owner ownerMember ownerActive
  have size:=nodeBytes_bounds (wordAt memory node)
  have ownerSize:=nodeBytes_bounds (wordAt memory owner)
  intro equal
  by_cases same : node=owner
  · subst node
    have cancelled : BitVec.ofNat 64 offset=BitVec.ofNat 64 cache:=(BitVec.add_right_inj owner).mp equal
    have numeric:=congrArg BitVec.toNat cancelled
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega),BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at numeric
    omega
  · have separate:=disjoint node member active owner ownerMember ownerActive same
    have firstNumber : (byteAddress node offset).toNat=node.toNat+offset:=byteAddress_toNat node offset (by have bound:=arena.upper; omega)
    have ownerNumber : (owner+BitVec.ofNat 64 cache).toNat=owner.toNat+cache:=byteAddress_toNat owner cache (by have bound:=ownerArena.upper; omega)
    have numeric:=congrArg BitVec.toNat equal
    rw [firstNumber,ownerNumber] at numeric
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Footprint.data_location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueFootprint.data_location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_field_away
