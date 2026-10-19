import InitECandidate.Solver.Mpt.TrieWalkValueAgreement

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix

variable {property : BitVec 64 → BitVec 64 → Prop}

theorem ValueFootprint.transport (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (next : Graph memory' domain') (validEq : next.valid=graph.valid)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt memory' node=wordAt memory node)
    (query : BitVec 64) (required : ValueFootprint next query) : ValueFootprint graph query := by
  cases required with
  | leafPointer node member active tag =>
    have oldMember : graph.valid node := by rwa [validEq] at member
    rw [tags node oldMember active] at tag
    exact .leafPointer node oldMember active tag
  | leafLength node member active tag =>
    have oldMember : graph.valid node := by rwa [validEq] at member
    rw [tags node oldMember active] at tag
    exact .leafLength node oldMember active tag
  | branchPointer node member active notHash notLeaf notExtension =>
    have oldMember : graph.valid node := by rwa [validEq] at member
    rw [tags node oldMember active] at notHash notLeaf notExtension
    exact .branchPointer node oldMember active notHash notLeaf notExtension
  | branchLength node member active notHash notLeaf notExtension =>
    have oldMember : graph.valid node := by rwa [validEq] at member
    rw [tags node oldMember active] at notHash notLeaf notExtension
    exact .branchLength node oldMember active notHash notLeaf notExtension

theorem Values.after_hash (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (valueLimit : Nat) (values : Values graph valueLimit property)
    (stp scratch out nibs : BitVec 64)
    (protectedGraph : graph.Protected nibs) (protectedValues : ValueProtected graph nibs)
    (hashProtection : ∀ query,graph.Footprint query → Keccak256.Protected stp scratch out query)
    (valueProtection : ∀ query,ValueFootprint graph query → Keccak256.Protected stp scratch out query)
    (control : KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp scratch out query → post.memory query=source.memory query) :
    ∃ nextGraph : Graph post.memory post.memaddrs,nextGraph.valid=graph.valid ∧ nextGraph.Protected nibs ∧
      ValueProtected nextGraph nibs ∧ Nonempty (Values nextGraph valueLimit property) := by
  obtain ⟨next,validEq,nextProtection⟩ := Graph.after_hash source post graph stp scratch out nibs protectedGraph hashProtection control memory
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs control
  change post.memaddrs=source.memaddrs at domainEq
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node := by
    intro node member active
    unfold wordAt
    rw [memory node (hashProtection node (.header node member active))]
  have nextValueProtection : ValueProtected next nibs := by
    intro query required
    exact protectedValues query (ValueFootprint.transport source.memory post.memory source.memaddrs post.memaddrs graph next validEq tags query required)
  exact ⟨next,validEq,nextProtection,nextValueProtection,⟨Values.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next valueLimit values validEq domainEq tags
    (fun query required => memory query (valueProtection query required))⟩⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ValueFootprint.transport
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.after_hash
