import InitECandidate.Solver.Mpt.TrieProtectedGrowth
import InitECandidate.Solver.Mpt.NodeConstructorPhysical
import InitECandidate.Solver.Mpt.NodeBranchPhysical

namespace InitECandidate.Solver.Mpt.NodeConstructor
open Flapjack PanSemStateFiniteExact WitnessRadix GasBudget

/-- The actual initialized leaf/extension fields derive protection of
every older caller word after registration. The borrowed path may be a
full old path or a query window; its real backing-word avoidance is used. -/
theorem Physical.path_protected (kind : Kind) (pathKind : kind=.leaf ∨ kind=.extension)
    (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64) (words : String→BitVec 64)
    (physical : Physical kind source target heap words)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (next : TrieWalk.Graph target.memory target.memaddrs)
    (nodeLower : Nat) (regions : graph.Regions nodeLower heap.toNat)
    (members : ∀ node,next.valid node ↔ graph.valid node ∨ node=heap)
    (query : BitVec 64) (safe : graph.ProtectedWord query) (before : query.toNat<heap.toNat)
    (pathAway : TrieWalk.PathWordAway (words "nib") (words "nlen").toNat query) :
    target.memory query=source.memory query ∧ next.ProtectedWord query := by
  have oldFields : graph.PathFields target.memory:=TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions
    (fun address below=>physical.memory address (Or.inl below))
  have tagCell : target.memory heap=.word (tag kind):=by
    have field : (⟨0,.literal (tag kind)⟩ : FieldStores.Field)∈fields kind words:=by
      rcases pathKind with rfl|rfl <;> simp [fields,tag]
    simpa only [FieldStores.Value.word,BitVec.add_zero] using physical.cells _ field
  have actualTag : wordAt target.memory heap=tag kind:=by simp [wordAt,tagCell,MemoryBytes.wordBits]
  have pointerCell : target.memory (heap+32#64)=.word (words "nib"):=by
    have field : (⟨32,.saved "nib" (words "nib")⟩ : FieldStores.Field)∈fields kind words:=by
      rcases pathKind with rfl|rfl <;> simp [fields]
    simpa only [FieldStores.Value.word] using physical.cells _ field
  have lengthCell : target.memory (heap+40#64)=.word (words "nlen"):=by
    have field : (⟨40,.saved "nlen" (words "nlen")⟩ : FieldStores.Field)∈fields kind words:=by
      rcases pathKind with rfl|rfl <;> simp [fields]
    simpa only [FieldStores.Value.word] using physical.cells _ field
  have arena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt target.memory heap)):=by
    rw [actualTag]
    rcases pathKind with rfl|rfl <;> simpa [tag,TrieWalk.nodeBytes,bytes] using physical.arena
  refine ⟨physical.memory query (Or.inl before),safe.after_fresh graph next query heap oldFields members before arena ?_⟩
  intro _path
  simpa only [wordAt,pointerCell,lengthCell,MemoryBytes.wordBits] using pathAway

/-- A genuinely initialized branch borrows no path at all. Its fresh
allocation and preserved old descriptors retain every older protected
caller word, regardless of where that word lies among older nodes. -/
theorem BranchPhysical.protected (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (heap : BitVec 64)
    (physical : BranchPhysical source target heap)
    (graph : TrieWalk.Graph source.memory source.memaddrs) (next : TrieWalk.Graph target.memory target.memaddrs)
    (nodeLower : Nat) (regions : graph.Regions nodeLower heap.toNat)
    (members : ∀ node,next.valid node ↔ graph.valid node ∨ node=heap)
    (query : BitVec 64) (safe : graph.ProtectedWord query) (before : query.toNat<heap.toNat) :
    target.memory query=source.memory query ∧ next.ProtectedWord query := by
  have oldFields : graph.PathFields target.memory:=TrieWalk.Graph.PathFields.of_prefix graph target.memory nodeLower heap.toNat regions
    (fun address below=>physical.allocation.memory address (Or.inl below))
  have actualTag : wordAt target.memory heap=3#64:=by simp [wordAt,physical.tag,MemoryBytes.wordBits]
  have arena : AllocatedBytes.Arena heap (TrieWalk.nodeBytes (wordAt target.memory heap)):=by
    simpa [actualTag,TrieWalk.nodeBytes,bytes] using physical.allocation.arena
  refine ⟨physical.allocation.memory query (Or.inl before),safe.after_fresh graph next query heap oldFields members before arena ?_⟩
  intro path
  rw [actualTag] at path
  rcases path with impossible|impossible <;> cases impossible

end InitECandidate.Solver.Mpt.NodeConstructor

#print axioms InitECandidate.Solver.Mpt.NodeConstructor.Physical.path_protected
#print axioms InitECandidate.Solver.Mpt.NodeConstructor.BranchPhysical.protected
