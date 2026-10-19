import InitECandidate.Solver.Mpt.TrieWalkValues
import InitECandidate.Solver.Mpt.TrieWalkInvariant

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

def Values.rebase (memory memory' : Memory) (domain domain' : BitVec 64 → Prop)
    (graph : Graph memory domain) (valueLimit : Nat) (values : Values graph valueLimit)
    (sameMemory : memory'=memory) (sameDomain : domain'=domain) :
    Values (Graph.rebase memory memory' domain domain' graph sameMemory sameDomain) valueLimit := by
  subst memory'
  subst domain'
  exact values

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Values.rebase
