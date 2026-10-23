import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel
import InitECandidate.Solver.Mpt.WitnessCorePathBranchMemory

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- A real pending-branch mutation and registration preserves all old
paths. The new branch contributes no path; its cells were already
separated from every old path while it was pending. -/
theorem NodeRegistry.PathModel.branch_registered (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap node : BitVec 64) (registry : NodeRegistry source frontier heap db)
    (next : NodeRegistry post frontier heap db) (paths : registry.PathModel) (frontierLower : 2713731432≤frontier)
    (arena : AllocatedBytes.Arena node 176) (excluded : registry.graph.Excludes node 176)
    (members : ∀ current,next.graph.valid current → registry.graph.valid current ∨ current=node)
    (tag : wordAt post.memory node=3#64) (domain : post.memaddrs=source.memaddrs) (endian : post.be=source.be)
    (memory : ∀ query : BitVec 64,2713731425≤query.toNat → (query.toNat<node.toNat ∨ node.toNat+176≤query.toNat) → post.memory query=source.memory query)
    (apart : ∀ current,registry.graph.valid current → current≠0#64 → (wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64) →
      ∀ index<(wordAt source.memory (current+40#64)).toNat,∀ offset<176,
        panByteAlignHOL (width:=64) (byteAddress (wordAt source.memory (current+32#64)) index)≠byteAddress node offset) : next.PathModel := by
  have agree : ∀ query,registry.graph.Footprint query → post.memory query=source.memory query:=by
    intro query required
    have bounds:=registry.graph.footprint_bounds frontier heap.toNat registry.regions query required
    exact memory query (by omega) (registry.graph.excluded_footprint frontier heap.toNat registry.regions node 176 excluded query required)
  have tags (current : BitVec 64) (member : registry.graph.valid current) (active : current≠0#64) : wordAt post.memory current=wordAt source.memory current:=by
    unfold wordAt
    rw [agree current (.header current member active)]
  have span (current : BitVec 64) (member : registry.graph.valid current) (active : current≠0#64)
      (pathTag : wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64) :
      TrieWalk.NibbleSpan post.memory post.memaddrs post.be (wordAt source.memory (current+32#64)) (wordAt source.memory (current+40#64)).toNat:=by
    have original:=paths.bytes.span current member active pathTag
    apply original.of_agreement source.memory post.memory source.memaddrs post.memaddrs source.be post.be _ _ domain endian
    intro index inside
    have bounds:=paths.regions current member active pathTag
    have number:=byteAddress_toNat (wordAt source.memory (current+32#64)) index (by have fits:=original.fits; omega)
    apply memory
    · rw [AllocatedBytes.aligned_number,number]
      omega
    · exact outside_node_of_away _ node 176 arena (apart current member active pathTag index inside)
  refine ⟨?_,?_,?_⟩
  · constructor
    · intro current member active pathTag
      rcases members current member with prior|fresh
      · have oldTag : wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64:=by rwa [tags current prior active] at pathTag
        have fields:=registry.graph.path_word_agreement post.memory agree current prior active oldTag
        rw [fields.1,fields.2]
        exact span current prior active oldTag
      · subst current
        rw [tag] at pathTag
        rcases pathTag with impossible|impossible <;> cases impossible
    · intro current member active extensionTag
      rcases members current member with prior|fresh
      · have oldTag : wordAt source.memory current=2#64:=by rwa [tags current prior active] at extensionTag
        rw [(registry.graph.path_word_agreement post.memory agree current prior active (Or.inr oldTag)).2]
        exact paths.bytes.positive current prior active oldTag
      · subst current
        rw [tag] at extensionTag
        cases extensionTag
  · intro current member active pathTag
    rcases members current member with prior|fresh
    · have oldTag : wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64:=by rwa [tags current prior active] at pathTag
      have fields:=registry.graph.path_word_agreement post.memory agree current prior active oldTag
      rw [fields.1,fields.2]
      exact paths.regions current prior active oldTag
    · subst current
      rw [tag] at pathTag
      rcases pathTag with impossible|impossible <;> cases impossible
  · intro current member active pathTag index inside owner ownerMember ownerActive offset offsetInside
    rcases members current member with prior|fresh
    · have oldTag : wordAt source.memory current=1#64 ∨ wordAt source.memory current=2#64:=by rwa [tags current prior active] at pathTag
      have fields:=registry.graph.path_word_agreement post.memory agree current prior active oldTag
      rw [fields.2] at inside
      rw [fields.1]
      rcases members owner ownerMember with ownerPrior|ownerFresh
      · rw [tags owner ownerPrior ownerActive] at offsetInside
        exact paths.separated current prior active oldTag index inside owner ownerPrior ownerActive offset offsetInside
      · subst owner
        rw [tag] at offsetInside
        exact apart current prior active oldTag index inside offset offsetInside
    · subst current
      rw [tag] at pathTag
      rcases pathTag with impossible|impossible <;> cases impossible

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.PathModel.branch_registered
