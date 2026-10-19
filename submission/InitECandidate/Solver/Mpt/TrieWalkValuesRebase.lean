import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.Mpt.TrieWalkInvariant

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

variable {property : BitVec 64 → BitVec 64 → Prop}

def Values.rebase (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (valueLimit : Nat) (values : Values graph valueLimit property)
    (sameMemory : memory'=memory) (sameDomain : domain'=domain) :
    Values (Graph.rebase memory memory' domain domain' graph sameMemory sameDomain) valueLimit property := by
  subst memory'
  subst domain'
  exact values

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.rebase
