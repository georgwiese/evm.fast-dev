import InitECandidate.Solver.Mpt.NodeBranchPhysical
import InitECandidate.Solver.Mpt.BranchRegistration
import InitECandidate.Solver.Mpt.TrieGraphPathPrefix
import InitECandidate.Solver.Mpt.TriePathBytesRegister

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- The actual branch allocation extends the closed graph while
preserving every stored path and its separation from mutable node cells. -/
theorem BranchPhysical.path_graph
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (physical : BranchPhysical source target heap) (domain : source.memaddrs=InitE.ordinaryDomain) (aligned : heap.toNat%8=0)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (limit nodeLower pathLower : Nat) (property : BitVec 64 → BitVec 64 → Prop)
    (values : TrieWalk.Values graph limit property) (regions : graph.Regions nodeLower heap.toNat) (disjoint : graph.Disjoint)
    (paths : graph.PathBytes source.be) (pathRegions : graph.PathRegions pathLower heap.toNat) (separated : graph.PathSeparated)
    (floor : nodeLower≤heap.toNat) (empty : property 0#64 0#64) :
    ∃ next : TrieWalk.Graph target.memory target.memaddrs,
      (∀ node,next.valid node ↔ graph.valid node ∨ node=heap) ∧ next.valid heap ∧
      next.Regions nodeLower (PersistentAlloc.rounded heap 176#64).toNat ∧ next.Disjoint ∧ Nonempty (TrieWalk.Values next limit property) ∧
      next.PathBytes target.be ∧ next.PathRegions pathLower (PersistentAlloc.rounded heap 176#64).toNat ∧ next.PathSeparated := by
  let allocation:=physical.allocation
  have memory : ∀ query : BitVec 64,query.toNat<heap.toNat → target.memory query=source.memory query:=
    fun query before=>allocation.memory query (Or.inl before)
  obtain ⟨base,same,baseRegions,baseDisjoint,⟨baseValues⟩,basePaths,basePathRegions,baseSeparated⟩:=
    graph.after_path_prefix source target limit nodeLower pathLower heap.toNat property values regions disjoint paths pathRegions separated allocation.domain allocation.endian memory
  have targetDomain : target.memaddrs=InitE.ordinaryDomain:=allocation.domain.trans domain
  have actualTag : wordAt target.memory heap=3#64:=by simp [wordAt,physical.tag,MemoryBytes.wordBits]
  have noPath : ¬(wordAt target.memory heap=1#64 ∨ wordAt target.memory heap=2#64):=by rw [actualTag]; decide
  let data:=TrieWalk.Registration.empty_branch target base heap targetDomain allocation.arena aligned physical.tag physical.zeros
  have newValue:=TrieWalk.ValueView.empty_branch target heap limit property empty targetDomain allocation.arena aligned physical.zeros
  have nodeArena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt target.memory heap)):=by
    simpa [actualTag,TrieWalk.nodeBytes,bytes] using allocation.arena
  have before : heap.toNat+TrieWalk.nodeBytes (wordAt target.memory heap)≤(PersistentAlloc.rounded heap 176#64).toNat:=by
    simpa [actualTag,TrieWalk.nodeBytes,bytes] using allocation.before
  have grows : heap.toNat≤(PersistentAlloc.rounded heap 176#64).toNat:=by omega
  let next:=base.register heap data
  have nextRegions : next.Regions nodeLower (PersistentAlloc.rounded heap 176#64).toNat:=
    TrieWalk.Graph.Regions.register base heap data nodeLower (PersistentAlloc.rounded heap 176#64).toNat
      (baseRegions.weaken base nodeLower heap.toNat nodeLower (PersistentAlloc.rounded heap 176#64).toNat (Nat.le_refl _) grows) floor nodeArena aligned before
  have nextDisjoint : next.Disjoint:=baseDisjoint.register base heap data (by
    intro old member active different
    exact Or.inr (baseRegions old member active).2.2.2)
  let nextValues:=TrieWalk.Values.register base heap data limit baseValues
    (fun tag=>(noPath (Or.inl tag)).elim) (fun _ _ _=>newValue)
  have nextPaths : next.PathBytes target.be:=basePaths.register base target.be heap data
    (fun tag=>(noPath tag).elim) (fun tag=>(noPath (Or.inr tag)).elim)
  have nextPathRegions : next.PathRegions pathLower (PersistentAlloc.rounded heap 176#64).toNat:=
    TrieWalk.Graph.PathRegions.register base pathLower (PersistentAlloc.rounded heap 176#64).toNat
      (basePathRegions.weaken base pathLower heap.toNat pathLower (PersistentAlloc.rounded heap 176#64).toNat (Nat.le_refl _) grows)
      heap data (fun tag=>(noPath tag).elim)
  have nextSeparated : next.PathSeparated:=baseSeparated.register base heap data (by
    intro current member active tag index inside nodeActive offset within
    exact (basePaths.span current member active tag).apart_before target.memory target.memaddrs target.be _ heap _ _ nodeArena
      (basePathRegions current member active tag).2 index inside offset within) (fun tag=>(noPath tag).elim)
  refine ⟨next,?_,Or.inr rfl,nextRegions,nextDisjoint,⟨nextValues⟩,nextPaths,nextPathRegions,nextSeparated⟩
  intro node
  change (base.valid node ∨ node=heap) ↔ (graph.valid node ∨ node=heap)
  rw [same]

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.BranchPhysical.path_graph
