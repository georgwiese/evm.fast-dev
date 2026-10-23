import InitECandidate.Solver.Mpt.TrieGraphPathFields
import InitECandidate.Solver.Mpt.TrieChildSlot

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget WitnessRadix

theorem Graph.PathFields.of_agreement {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (memory' : Memory)
    (agree : ∀ query,graph.Footprint query→memory' query=memory query) : graph.PathFields memory' := by
  constructor
  · intro node member active
    exact congrArg MemoryBytes.wordBits (agree node (.header node member active))
  · intro node member active tag
    exact graph.path_word_agreement memory' agree node member active tag

theorem Graph.PathFields.of_prefix {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (memory' : Memory) (lower upper : Nat)
    (regions : graph.Regions lower upper)
    (agree : ∀ query : BitVec 64,query.toNat<upper→memory' query=memory query) : graph.PathFields memory' :=
  Graph.PathFields.of_agreement graph memory' (by intro query required; exact agree query (graph.footprint_bounds lower upper regions query required).2)

/-- Child replacement changes neither saved parent tags nor their path
pointer/length fields, including when the replacement aliases an ancestor. -/
theorem Graph.PathFields.of_child_store {memory : Memory} {domain : BitVec 64→Prop}
    (graph : Graph memory domain) (lower upper : Nat) (regions : graph.Regions lower upper) (disjoint : graph.Disjoint)
    (owner child : BitVec 64) (offset : Nat) (slot : ChildSlot memory owner offset)
    (member : graph.valid owner) (active : owner≠0#64) :
    graph.PathFields (StoreWord.put memory (owner+BitVec.ofNat 64 offset) child) := by
  constructor
  · intro node nodeMember nodeActive
    exact congrArg MemoryBytes.wordBits (if_neg (graph.child_store_header_away lower upper regions disjoint owner offset slot member active node nodeMember nodeActive))
  · intro node nodeMember nodeActive tag
    have away:=graph.child_store_path_away lower upper regions disjoint owner offset slot member active node nodeMember nodeActive tag
    exact ⟨congrArg MemoryBytes.wordBits (if_neg away.1),congrArg MemoryBytes.wordBits (if_neg away.2)⟩

/-- Compose actual field frames through a registry that may have acquired
new nodes, retaining every earlier saved parent. -/
theorem Graph.PathFields.trans {memory middle final : Memory} {domain middleDomain : BitVec 64→Prop}
    (graph : Graph memory domain) (next : Graph middle middleDomain)
    (first : graph.PathFields middle) (second : next.PathFields final)
    (members : ∀ node,graph.valid node→next.valid node) : graph.PathFields final := by
  constructor
  · intro node member active
    exact (second.tags node (members node member) active).trans (first.tags node member active)
  · intro node member active tag
    have currentTag : wordAt middle node=1#64 ∨ wordAt middle node=2#64:=by rw [first.tags node member active]; exact tag
    have before:=first.fields node member active tag
    have after:=second.fields node (members node member) active currentTag
    exact ⟨after.1.trans before.1,after.2.trans before.2⟩

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.of_agreement
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.of_prefix
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.of_child_store
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.PathFields.trans
