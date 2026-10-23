import InitECandidate.Solver.Mpt.TrieProtectedWord
import InitECandidate.Solver.Mpt.NodeInvalidate
import InitECandidate.Solver.Mpt.BranchValueUpdateProgram
import InitECandidate.Solver.Mpt.LeafUpdateProgram

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

/-- An actual initialized child-slot write cannot touch a separated
caller word, including a header between old and newly allocated nodes. -/
theorem Graph.ProtectedWord.child_memory {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (query owner child : BitVec 64) (offset : Nat)
    (word : graph.ProtectedWord query) (member : graph.valid owner) (active : owner≠0#64)
    (slot : ChildSlot memory owner offset) :
    StoreWord.put memory (owner+BitVec.ofNat 64 offset) child query=memory query :=
  if_neg (word.nodes owner member active offset (slot.bounds memory owner offset).2.2.1)

/-- The literal three cache clears preserve every current protected
caller word. Only the actual registered owner's extent is used. -/
theorem Graph.ProtectedWord.invalidate_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (query owner : BitVec 64)
    (word : graph.ProtectedWord query) (member : graph.valid owner) (active : owner≠0#64) :
    (NodeInvalidate.post source owner).memory query=source.memory query := by
  have size:=(nodeBytes_bounds (wordAt source.memory owner)).1
  exact NodeInvalidate.post_away source owner query
    (word.nodes owner member active 8 (by omega)) (word.nodes owner member active 16 (by omega)) (word.nodes owner member active 24 (by omega))

/-- The actual branch-value pair writes preserve a separated header,
whether they clear the value or install a current payload. -/
theorem Graph.ProtectedWord.branch_value_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (query owner pointer size : BitVec 64)
    (word : graph.ProtectedWord query) (member : graph.valid owner) (active : owner≠0#64)
    (tag : wordAt source.memory owner=3#64) :
    (BranchValueUpdate.post source owner pointer size).memory query=source.memory query :=
  BranchValueUpdate.post_away source owner pointer size query
    (word.nodes owner member active 160 (by rw [tag]; decide)) (word.nodes owner member active 168 (by rw [tag]; decide))

/-- Matching-leaf replacement changes only its real48/56 value fields,
which lie outside every currently separated caller header word. -/
theorem Graph.ProtectedWord.leaf_value_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (graph : Graph source.memory source.memaddrs) (query owner pointer size : BitVec 64)
    (word : graph.ProtectedWord query) (member : graph.valid owner) (active : owner≠0#64)
    (tag : wordAt source.memory owner=1#64) :
    (InsertLeaf.post source owner pointer size).memory query=source.memory query :=
  InsertLeaf.post_away source owner pointer size query
    (word.nodes owner member active 48 (by rw [tag]; decide)) (word.nodes owner member active 56 (by rw [tag]; decide))

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.child_memory
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.invalidate_memory
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.branch_value_memory
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.ProtectedWord.leaf_value_memory
