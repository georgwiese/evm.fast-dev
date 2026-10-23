import InitECandidate.Solver.Mpt.TrieChildSlot

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- Only the actual node tag determines whether an address is a child slot. -/
theorem ChildSlot.of_tag (memory nextMemory : Memory) (owner : BitVec 64) (offset : Nat)
    (slot : ChildSlot memory owner offset) (tag : wordAt nextMemory owner=wordAt memory owner) :
    ChildSlot nextMemory owner offset := by
  cases slot with
  | extension old=>exact .extension (tag.trans old)
  | branch notHash notLeaf notExtension index inside=>
    exact .branch (by rw [tag]; exact notHash) (by rw [tag]; exact notLeaf) (by rw [tag]; exact notExtension) index inside

/-- The insertion loop either updates its local root or an actual
registered parent child slot. Shared parents and cycles are permitted. -/
def Graph.ParentSlot {memory : Memory} {domain : BitVec 64 → Prop} (graph : Graph memory domain) (address : BitVec 64) : Prop:=
  address=0#64 ∨ ∃ owner offset,graph.valid owner ∧ owner≠0#64 ∧ ChildSlot memory owner offset ∧ address=owner+BitVec.ofNat 64 offset

theorem Graph.ParentSlot.of_tags {memory nextMemory : Memory} {domain nextDomain : BitVec 64 → Prop}
    (graph : Graph memory domain) (next : Graph nextMemory nextDomain) (address : BitVec 64) (slot : graph.ParentSlot address)
    (members : ∀ node,graph.valid node → next.valid node)
    (tags : ∀ node,graph.valid node → node≠0#64 → wordAt nextMemory node=wordAt memory node) : next.ParentSlot address := by
  rcases slot with zero|⟨owner,offset,member,active,selected,equal⟩
  · exact Or.inl zero
  · exact Or.inr ⟨owner,offset,members owner member,active,selected.of_tag memory nextMemory owner offset (tags owner member active),equal⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.ChildSlot.of_tag
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ParentSlot.of_tags
