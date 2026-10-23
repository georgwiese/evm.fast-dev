import InitECandidate.Solver.Mpt.TrieGraphStorageFrame
import InitECandidate.Solver.Mpt.TriePathBuffer

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Real writes at or above the current heap retain all older node
fields, payload contracts and full stored path buffers. -/
theorem Graph.after_path_prefix (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (limit lower pathLower upper : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : Values graph limit property) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (memory : ∀ query : BitVec 64,query.toNat<upper → target.memory query=source.memory query) :
    ∃ next : Graph target.memory target.memaddrs,next.valid=graph.valid ∧ next.Regions lower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes target.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  have agree : ∀ query,graph.Footprint query → target.memory query=source.memory query:=by
    intro query required
    exact memory query (graph.footprint_bounds lower upper regions query required).2
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_agreement source target limit lower upper property values regions disjoint domain agree
    (fun query required=>memory query (graph.value_bounds lower upper regions query required).2)
  have byteAgreement : ∀ node,graph.valid node → node≠0#64 → (wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64) →
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
        target.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    let pointer:=wordAt source.memory (node+32#64)
    let length:=(wordAt source.memory (node+40#64)).toNat
    have span : NibbleSpan source.memory source.memaddrs source.be pointer length:=paths.span node member active tag
    have bounds : pathLower≤pointer.toNat ∧ pointer.toNat+length≤upper:=pathRegions node member active tag
    have number:=byteAddress_toNat pointer index (by have fits:=span.fits; omega)
    apply memory
    change (panByteAlignHOL (width:=64) (byteAddress pointer index)).toNat<upper
    rw [AllocatedBytes.aligned_number,number]
    omega
  exact ⟨next,same,nextRegions,nextDisjoint,nextValues,
    paths.of_agreement source.memory target.memory source.memaddrs target.memaddrs source.be target.be graph next same domain endian agree byteAgreement,
    pathRegions.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next pathLower upper same agree,
    separated.of_agreement source.memory target.memory source.memaddrs target.memaddrs graph next same agree⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_path_prefix
