import InitECandidate.Solver.Mpt.TrieWalkMemory

namespace InitECandidate.Solver.Mpt.TrieWalk
open Flapjack PanSemStateFiniteExact GasBudget

/-- Registered tags come from actual original initialization and survive
all registered graph transformations. No arbitrary branch tag is possible. -/
theorem Graph.kind_cases {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) (member : graph.valid node) (active : node≠0#64) :
    wordAt memory node=0#64 ∨ wordAt memory node=1#64 ∨ wordAt memory node=2#64 ∨ wordAt memory node=3#64 := by
  have bound:=graph.kindBound node member active
  have numbers : (wordAt memory node).toNat=0 ∨ (wordAt memory node).toNat=1 ∨ (wordAt memory node).toNat=2 ∨ (wordAt memory node).toNat=3:=by omega
  rcases numbers with zero|one|two|three
  · exact Or.inl (BitVec.eq_of_toNat_eq zero)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq one))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq two)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq three)))

theorem Graph.branch_kind {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt memory node≠0#64) (notLeaf : wordAt memory node≠1#64) (notExtension : wordAt memory node≠2#64) :
    wordAt memory node=3#64 :=
  (((graph.kind_cases node member active).resolve_left notHash).resolve_left notLeaf).resolve_left notExtension

theorem Graph.path_kind {memory : Memory} {domain : BitVec 64 → Prop}
    (graph : Graph memory domain) (node : BitVec 64) (member : graph.valid node) (active : node≠0#64)
    (notHash : wordAt memory node≠0#64) (notBranch : wordAt memory node≠3#64) :
    wordAt memory node=1#64 ∨ wordAt memory node=2#64 := by
  rcases (graph.kind_cases node member active).resolve_left notHash with leaf|extension|branch
  · exact Or.inl leaf
  · exact Or.inr extension
  · exact (notBranch branch).elim

end InitECandidate.Solver.Mpt.TrieWalk

#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.kind_cases
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.branch_kind
#print axioms InitECandidate.Solver.Mpt.TrieWalk.Graph.path_kind
