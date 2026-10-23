import InitECandidate.Solver.Mpt.TrieGraphPathFieldsFrame
import InitECandidate.Solver.Mpt.TrieGraphPathBand

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A caller-owned word outside every live node allocation and all
stored-path backing words. This permits a header allocated after some
nodes and before others; no global address order is imposed. -/
structure Graph.ProtectedWord {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query : BitVec 64) : Prop where
  nodes : ∀ node,graph.valid node→node≠0#64→∀ offset<nodeBytes (wordAt memory node),query≠byteAddress node offset
  paths : ∀ node,graph.valid node→node≠0#64→(wordAt memory node=1#64 ∨ wordAt memory node=2#64)→
    ∀ index<(wordAt memory (node+40#64)).toNat,query≠panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index)

/-- A newly allocated caller object follows the entire current graph
and stored paths. Each of its words is protected, independently of later
fresh-node allocations above that object. -/
theorem Graph.ProtectedWord.above_regions {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (be : Bool) (nodeLower pathLower upper : Nat) (query : BitVec 64)
    (regions : graph.Regions nodeLower upper) (paths : graph.PathBytes be) (pathRegions : graph.PathRegions pathLower upper)
    (above : upper≤query.toNat) : graph.ProtectedWord query := by
  constructor
  · intro node member active offset inside equal
    have bounds:=regions node member active
    have number:=byteAddress_toNat node offset (by have upper:=bounds.2.1.upper; omega)
    have same:=congrArg BitVec.toNat equal
    rw [number] at same
    omega
  · intro node member active tag index inside equal
    have bounds:=pathRegions node member active tag
    have span:=paths.span node member active tag
    have number:=byteAddress_toNat (wordAt memory (node+32#64)) index (by have fits:=span.fits; omega)
    have backing : (panByteAlignHOL (width:=64) (byteAddress (wordAt memory (node+32#64)) index)).toNat≤
        (byteAddress (wordAt memory (node+32#64)) index).toNat:=by rw [AllocatedBytes.aligned_number]; omega
    have same:=congrArg BitVec.toNat equal
    rw [number] at backing
    omega

/-- Current saved node/path descriptors retain protection when the same
registry is transported through real metadata/value/child mutations. -/
theorem Graph.ProtectedWord.of_fields {memory memory' : Memory} {domain domain' : BitVec 64→Prop}
    (graph : Graph memory domain) (next : Graph memory' domain') (query : BitVec 64)
    (word : graph.ProtectedWord query) (same : next.valid=graph.valid) (fields : graph.PathFields memory') : next.ProtectedWord query := by
  constructor
  · intro node member active offset inside
    have oldMember : graph.valid node:=by rwa [same] at member
    rw [fields.tags node oldMember active] at inside
    exact word.nodes node oldMember active offset inside
  · intro node member active tag index inside
    have oldMember : graph.valid node:=by rwa [same] at member
    have oldTag : wordAt memory node=1#64 ∨ wordAt memory node=2#64:=by rwa [fields.tags node oldMember active] at tag
    have descriptor:=fields.fields node oldMember active oldTag
    rw [descriptor.2] at inside
    rw [descriptor.1]
    exact word.paths node oldMember active oldTag index inside

/-- The actual caller-word store preserves the full physical trie and
all stored nibble paths whenever the current separation proves it safe. -/
theorem Graph.after_protected_store (source : PanSemStateFiniteExact 64 Guest.HostMemory) (query value : BitVec 64)
    (graph : Graph source.memory source.memaddrs) (limit nodeLower pathLower upper : Nat) (property : BitVec 64→BitVec 64→Prop)
    (values : Values graph limit property) (regions : graph.Regions nodeLower upper) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower upper) (separated : graph.PathSeparated)
    (word : graph.ProtectedWord query) :
    let post:={source with memory:=StoreWord.put source.memory query value}
    graph.PathFields post.memory ∧ ∃ next : Graph post.memory post.memaddrs,next.valid=graph.valid ∧ next.Regions nodeLower upper ∧ next.Disjoint ∧
      Nonempty (Values next limit property) ∧ next.PathBytes post.be ∧ next.PathRegions pathLower upper ∧ next.PathSeparated := by
  let post:={source with memory:=StoreWord.put source.memory query value}
  have agree : ∀ address,graph.Footprint address→post.memory address=source.memory address:=by
    intro address required
    obtain ⟨node,offset,member,active,inside,_notCache,equal⟩:=required.location graph address
    exact if_neg (fun same=>word.nodes node member active offset inside (same.symm.trans equal))
  have valueAgree : ∀ address,ValueFootprint graph address→post.memory address=source.memory address:=by
    intro address required
    obtain ⟨node,offset,member,active,inside,_notCache,equal⟩:=required.location graph address
    exact if_neg (fun same=>word.nodes node member active offset inside (same.symm.trans equal))
  obtain ⟨next,same,nextRegions,nextDisjoint,nextValues⟩:=graph.after_agreement source post limit nodeLower upper property values regions disjoint rfl agree valueAgree
  have byteAgreement : ∀ node,graph.valid node→node≠0#64→(wordAt source.memory node=1#64 ∨ wordAt source.memory node=2#64)→
      ∀ index<(wordAt source.memory (node+40#64)).toNat,
      post.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index))=
        source.memory (panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (node+32#64)) index)):=by
    intro node member active tag index inside
    exact if_neg (word.paths node member active tag index inside).symm
  exact ⟨Graph.PathFields.of_agreement graph post.memory agree,next,same,nextRegions,nextDisjoint,nextValues,
    paths.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be graph next same rfl rfl agree byteAgreement,
    pathRegions.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next pathLower upper same agree,
    separated.of_agreement source.memory post.memory source.memaddrs post.memaddrs graph next same agree⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.above_regions
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.of_fields
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.after_protected_store
