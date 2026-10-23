import InitECandidate.Solver.Mpt.TriePathBufferPrefix

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Older query bytes survive a helper that writes only fresh heap
storage. Newly registered nodes are physically above that older buffer,
so it remains separated from every mutable node in the enlarged graph. -/
theorem Graph.PathBuffer.of_growing_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (lower oldUpper newUpper nodeLower : Nat) (pointer : BitVec 64) (length : Nat)
    (buffer : graph.PathBuffer source.be lower oldUpper pointer length)
    (regions : graph.Regions nodeLower oldUpper) (nextRegions : next.Regions nodeLower newUpper)
    (members : ∀ node,next.valid node→graph.valid node ∨ oldUpper≤node.toNat)
    (grows : oldUpper≤newUpper) (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<oldUpper→target.memory query=source.memory query) :
    next.PathBuffer target.be lower newUpper pointer length := by
  refine ⟨buffer.span.of_before source target pointer length oldUpper buffer.bounds.2 domain endian memory,
    ⟨buffer.bounds.1,buffer.bounds.2.trans grows⟩,?_⟩
  intro index inside owner member active offset within
  rcases members owner member with old|fresh
  · have before : owner.toNat<oldUpper:=by
      have bound:=(regions owner old active).2.2.2
      have size:=nodeBytes_bounds (wordAt source.memory owner)
      omega
    have tagEq : wordAt target.memory owner=wordAt source.memory owner:=congrArg MemoryBytes.wordBits (memory owner before)
    rw [tagEq] at within
    exact buffer.apart index inside owner old active offset within
  · intro same
    have byteNumber:=byteAddress_toNat pointer index (by have fits:=buffer.span.fits; omega)
    have ownerGeometry:=nextRegions owner member active
    have ownerNumber:=byteAddress_toNat owner offset (by have fits:=ownerGeometry.2.1.upper; omega)
    have equal:=congrArg BitVec.toNat same
    rw [AllocatedBytes.aligned_number,byteNumber,ownerNumber] at equal
    have before:=buffer.bounds.2
    omega

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.of_growing_prefix
