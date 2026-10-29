import InitECandidate.Solver.Mpt.TrieWalkGraphProtection
import InitECandidate.Solver.WitnessRadix.Keccak256CurrentCall

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget
open WitnessRadix

/-- Reconstruct the incoming trie graph after real hash writes, retaining
its protection from the separate nibble-conversion buffer. -/
theorem Graph.after_hash (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (stp scratch out nibs : BitVec 64)
    (protectedGraph : graph.Protected nibs)
    (hashProtection : ∀ query,graph.Footprint query → Keccak256.Protected stp scratch out query)
    (control : KeccakAbsorb.hashControl post=KeccakAbsorb.hashControl source)
    (memory : ∀ query,Keccak256.Protected stp scratch out query → post.memory query=source.memory query) :
    ∃ nextGraph : Graph post.memory post.memaddrs,nextGraph.valid=graph.valid ∧ nextGraph.Protected nibs := by
  have domainEq := congrArg PanSemStateFiniteExact.memaddrs control
  change post.memaddrs=source.memaddrs at domainEq
  have agree : ∀ query,graph.Footprint query → post.memory query=source.memory query := by
    intro query required
    exact memory query (hashProtection query required)
  let nextGraph := Graph.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph domainEq agree
  have validEq : nextGraph.valid=graph.valid := rfl
  have tags : ∀ node,graph.valid node → node≠0#64 → wordAt post.memory node=wordAt source.memory node := by
    intro node member active
    unfold wordAt
    rw [agree node (.header node member active)]
  refine ⟨nextGraph,validEq,?_⟩
  intro query required
  exact protectedGraph query (Graph.footprint_transport source.memory post.memory source.memaddrs post.memaddrs graph nextGraph validEq tags query required)

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.footprint_transport
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_hash
