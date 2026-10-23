import InitECandidate.Solver.Mpt.TrieProtectedWord

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Every word below an aligned lower frontier is outside the current
nodes and all full path backing words. Stored paths themselves may be
unaligned slices; only the caller's fixed band boundary is aligned. -/
theorem Graph.ProtectedWord.below_regions {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (be : Bool) (nodeLower pathLower upper cutoff : Nat) (query : BitVec 64)
    (regions : graph.Regions nodeLower upper) (paths : graph.PathBytes be) (pathRegions : graph.PathRegions pathLower upper)
    (aligned : cutoff%8=0) (nodesAbove : cutoff≤nodeLower) (pathsAbove : cutoff≤pathLower) (before : query.toNat<cutoff) :
    graph.ProtectedWord query := by
  constructor
  · intro node live active offset inside equal
    have bounds:=regions node live active
    have number:=byteAddress_toNat node offset (by have upper:=bounds.2.1.upper; omega)
    have same:=congrArg BitVec.toNat equal
    rw [number] at same
    omega
  · intro node live active tag index inside equal
    have bounds:=pathRegions node live active tag
    have span:=paths.span node live active tag
    have number:=byteAddress_toNat (wordAt memory (node+32#64)) index (by have fits:=span.fits; omega)
    have same:=congrArg BitVec.toNat equal
    rw [AllocatedBytes.aligned_number,number] at same
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.below_regions
