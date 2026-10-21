import InitECandidate.Solver.Mpt.TrieWalkValueAgreement

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

def nodeBytes (tag : BitVec 64) : Nat :=
  if tag=0#64 then 32 else if tag=1#64 then 64 else if tag=2#64 then 56 else 176

theorem nodeBytes_bounds (tag : BitVec 64) : 32≤nodeBytes tag ∧ nodeBytes tag≤176 := by
  unfold nodeBytes
  constructor <;> repeat' first | split | omega

/-- Real allocation extents for completed registered nodes. The cache
word is inside its owner's extent but outside all structural/value fields. -/
def Graph.Regions {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) : Prop :=
  ∀ node,graph.valid node→node≠0#64→lower≤node.toNat ∧ AllocatedBytes.Arena node (nodeBytes (wordAt memory node)) ∧
    node.toNat%8=0 ∧ node.toNat+nodeBytes (wordAt memory node)≤upper

def Graph.Disjoint {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) : Prop :=
  ∀ first,graph.valid first→first≠0#64→∀ second,graph.valid second→second≠0#64→first≠second→
    first.toNat+nodeBytes (wordAt memory first)≤second.toNat ∨ second.toNat+nodeBytes (wordAt memory second)≤first.toNat

theorem Graph.Footprint.location {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (query : BitVec 64) (required : graph.Footprint query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧ offset≠24 ∧ query=byteAddress node offset := by
  cases required with
  | header node member active=>exact ⟨query,0,member,active,by have bound:=nodeBytes_bounds (wordAt memory query); omega,by decide,by simp [byteAddress]⟩
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

theorem ValueFootprint.location {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (query : BitVec 64) (required : ValueFootprint graph query) :
    ∃ node offset,graph.valid node ∧ node≠0#64 ∧ offset<nodeBytes (wordAt memory node) ∧ offset≠24 ∧ query=byteAddress node offset := by
  cases required with
  | leafPointer node member active tag=>exact ⟨node,48,member,active,by rw [tag]; decide,by decide,rfl⟩
  | leafLength node member active tag=>exact ⟨node,56,member,active,by rw [tag]; decide,by decide,rfl⟩
  | branchPointer node member active notHash notLeaf notExtension=>
    exact ⟨node,160,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide,by decide,rfl⟩
  | branchLength node member active notHash notLeaf notExtension=>
    exact ⟨node,168,member,active,by simp only [nodeBytes,if_neg notHash,if_neg notLeaf,if_neg notExtension]; decide,by decide,rfl⟩

theorem Graph.region_query_bounds {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (node : BitVec 64) (offset : Nat) (member : graph.valid node) (active : node≠0#64)
    (inside : offset<nodeBytes (wordAt memory node)) :
    lower≤(byteAddress node offset).toNat ∧ (byteAddress node offset).toNat<upper := by
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  rw [byteAddress_toNat node offset (by have bound:=arena.upper; omega)]
  omega

theorem Graph.footprint_bounds {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (query : BitVec 64) (required : graph.Footprint query) : lower≤query.toNat ∧ query.toNat<upper := by
  obtain ⟨node,offset,member,active,inside,notCache,equal⟩:=required.location graph query
  rw [equal]
  exact graph.region_query_bounds lower upper regions node offset member active inside

theorem Graph.value_bounds {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper)
    (query : BitVec 64) (required : ValueFootprint graph query) : lower≤query.toNat ∧ query.toNat<upper := by
  obtain ⟨node,offset,member,active,inside,notCache,equal⟩:=required.location graph query
  rw [equal]
  exact graph.region_query_bounds lower upper regions node offset member active inside

/-- A node's cache cannot alias any registered structural or value word,
including its own, even when its child graph contains repeated pointers. -/
theorem Graph.cache_away {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner node : BitVec 64) (offset : Nat) (ownerMember : graph.valid owner) (ownerActive : owner≠0#64)
    (member : graph.valid node) (active : node≠0#64) (inside : offset<nodeBytes (wordAt memory node)) (notCache : offset≠24) :
    byteAddress node offset≠owner+24#64 := by
  obtain ⟨floor,arena,aligned,before⟩:=regions node member active
  obtain ⟨ownerFloor,ownerArena,ownerAligned,ownerBefore⟩:=regions owner ownerMember ownerActive
  have size:=nodeBytes_bounds (wordAt memory node)
  have ownerSize:=nodeBytes_bounds (wordAt memory owner)
  intro equal
  by_cases same : node=owner
  · subst node
    have cancelled : BitVec.ofNat 64 offset=24#64 := (BitVec.add_right_inj owner).mp equal
    have numeric:=congrArg BitVec.toNat cancelled
    rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)] at numeric
    exact notCache numeric
  · have separated:=disjoint node member active owner ownerMember ownerActive same
    have firstNumber : (byteAddress node offset).toNat=node.toNat+offset := byteAddress_toNat node offset (by have bound:=arena.upper; omega)
    have ownerNumber : (owner+24#64).toNat=owner.toNat+24 := byteAddress_toNat owner 24 (by have bound:=ownerArena.upper; omega)
    have numeric:=congrArg BitVec.toNat equal
    rw [firstNumber,ownerNumber] at numeric
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.Footprint.location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueFootprint.location
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.footprint_bounds
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.value_bounds
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.cache_away
