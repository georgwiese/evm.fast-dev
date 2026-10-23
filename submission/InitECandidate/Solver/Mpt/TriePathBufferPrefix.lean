import InitECandidate.Solver.Mpt.TrieGraphPathPrefix

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.PathBuffer.of_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (lower upper nodeLower : Nat) (pointer : BitVec 64) (length : Nat)
    (buffer : graph.PathBuffer source.be lower upper pointer length) (regions : graph.Regions nodeLower upper)
    (validEq : next.valid=graph.valid) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<upper → target.memory query=source.memory query) :
    next.PathBuffer target.be lower upper pointer length := by
  refine ⟨buffer.span.of_before source target pointer length upper buffer.bounds.2 domain endian memory,buffer.bounds,?_⟩
  intro index inside owner member active offset within
  have oldMember : graph.valid owner:=by rwa [validEq] at member
  have bounds:=regions owner oldMember active
  have tagEq : wordAt target.memory owner=wordAt source.memory owner:=by
    unfold wordAt
    rw [memory owner (by have size:=(nodeBytes_bounds (wordAt source.memory owner)).1; omega)]
  rw [tagEq] at within
  exact buffer.apart index inside owner oldMember active offset within

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.of_prefix
