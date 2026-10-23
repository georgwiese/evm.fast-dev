import InitECandidate.Solver.Mpt.TrieGraphPathPrefix
import InitECandidate.Solver.Mpt.TriePathBytesAlignedBand

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Low scratch writes leave the complete persistent registry intact.
Only the lower band boundary is aligned; stored paths may be slices. -/
theorem Graph.after_path_band (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower pathLower upper cutoff : Nat)
    (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (aligned : cutoff%8=0) (nodesAbove : cutoff≤lower) (pathsAbove : cutoff≤pathLower)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,cutoff≤query.toNat→query.toNat<upper→target.memory query=source.memory query) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  have agree : ∀ query,graph.Footprint query → target.memory query=source.memory query:=by
    intro query required
    have bounds:=graph.footprint_bounds lower upper regions query required
    exact memory query (by omega) bounds.2
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_agreement source target limit lower upper property values regions disjoint domain agree
    (by intro query required; have bounds:=graph.value_bounds lower upper regions query required; exact memory query (by omega) bounds.2)
  have byteAgreement : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        target.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    have span:=paths.span node member active tag
    have bounds:=pathRegions node member active tag
    have number:=byteAddress_toNat (wordAt source.memory (node+32#64)) index (by have fits:=span.fits; omega)
    apply memory
    · rw [AllocatedBytes.aligned_number,number]; omega
    · rw [AllocatedBytes.aligned_number,number]; omega
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,
    paths.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be graph next same domain endian agree byteAgreement,
    pathRegions.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next pathLower upper same agree,
    separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next same agree⟩

/-- The actual query buffer shares the persistent band with the old
paths. Retaining its full backing words also retains node separation. -/
theorem Graph.PathBuffer.of_aligned_band (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (next : Graph target.memory target.memaddrs)
    (lower upper cutoff : Nat) (pointer : BitVec 64) (length : Nat)
    (buffer : graph.PathBuffer source.be lower upper pointer length)
    (same : next.valid=graph.valid) (tags : ∀ node,graph.valid node→node≠0#64→wordAt target.memory node=wordAt source.memory node)
    (aligned : cutoff%8=0) (above : cutoff≤lower)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,cutoff≤query.toNat→query.toNat<upper→target.memory query=source.memory query) :
    next.PathBuffer target.be lower upper pointer length := by
  refine ⟨buffer.span.of_aligned_band source target pointer length cutoff upper aligned
    (above.trans buffer.bounds.1) buffer.bounds.2 domain endian memory,buffer.bounds,?_⟩
  intro index inside owner member active offset offsetInside
  have oldMember : graph.valid owner:=by rwa [same] at member
  rw [tags owner oldMember active] at offsetInside
  exact buffer.apart index inside owner oldMember active offset offsetInside

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_path_band
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathBuffer.of_aligned_band
