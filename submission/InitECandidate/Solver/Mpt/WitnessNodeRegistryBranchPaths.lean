import InitECandidate.Solver.Mpt.WitnessCoreRegistryConstructors
import InitECandidate.Solver.Mpt.WitnessNodeRegistryPathModel

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Registering an actual completed branch adds no path buffer. Its
previous pending-branch separation protects all old completed path bytes. -/
theorem NodeRegistry.branch_result_paths (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frontier : Nat) (db heap node : BitVec 64) (registry : NodeRegistry post frontier heap db) (paths : registry.PathModel)
    (children : Children post registry.graph.valid node 16)
    (value : TrieWalk.ValueView post.memory post.memaddrs node 160#64 168#64 1024 (WitnessValue db))
    (domain : post.memaddrs=InitE.ordinaryDomain) (arena : AllocatedBytes.Arena node 176) (aligned : node.toNat%8=0)
    (stored : post.memory node=.word 3#64) (floor : frontier≤node.toNat) (before : node.toNat+176≤heap.toNat)
    (excluded : registry.graph.Excludes node 176)
    (apart : ∀ current,registry.graph.valid current → current≠0#64 → (wordAt post.memory current=1#64 ∨ wordAt post.memory current=2#64) →
      ∀ index<(wordAt post.memory (current+40#64)).toNat,∀ offset<176,
        panByteAlignHOL (width:=64) (byteAddress (wordAt post.memory (current+32#64)) index)≠byteAddress node offset) :
    ∃ next : NodeRegistry post frontier heap db,next.PathModel ∧ next.graph.valid node ∧
      (∀ pointer,registry.graph.valid pointer → next.graph.valid pointer) ∧
      (∀ pointer,next.graph.valid pointer → registry.graph.valid pointer ∨ pointer=node) := by
  let data:=children.registration post registry.graph node domain arena aligned stored
  have tag : wordAt post.memory node=3#64:=by simp [wordAt,stored,MemoryBytes.wordBits]
  have leaf : wordAt post.memory node=1#64 → TrieWalk.ValueView post.memory post.memaddrs node 48#64 56#64 1024 (WitnessValue db):=by
    intro impossible; rw [tag] at impossible; cases impossible
  let registered:=registry.register post frontier heap db node data leaf (fun _ _ _=>value) floor
    (by rw [tag]; change AllocatedBytes.Arena node 176; exact arena) aligned (by rw [tag]; change node.toNat+176≤heap.toNat; exact before)
    (by simpa only [tag,show TrieWalk.nodeBytes 3#64=176 from by decide] using excluded)
  have currentPaths : registered.PathModel:=by
    refine ⟨paths.bytes.register registry.graph post.be node data ?_ ?_,
      paths.regions.register registry.graph frontier heap.toNat node data ?_,
      paths.separated.register registry.graph node data ?_ ?_⟩
    · intro pathTag
      rw [tag] at pathTag
      rcases pathTag with impossible|impossible <;> cases impossible
    · intro impossible
      rw [tag] at impossible
      cases impossible
    · intro pathTag
      rw [tag] at pathTag
      rcases pathTag with impossible|impossible <;> cases impossible
    · intro current member active pathTag index inside nodeActive offset offsetInside
      rw [tag] at offsetInside
      exact apart current member active pathTag index inside offset offsetInside
    · intro pathTag
      rw [tag] at pathTag
      rcases pathTag with impossible|impossible <;> cases impossible
  exact ⟨registered,currentPaths,Or.inr rfl,fun _ member=>Or.inl member,fun _ member=>member⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.NodeRegistry.branch_result_paths
