import InitECandidate.Solver.WitnessRadix.OpenGraphReplace

namespace InitECandidate.Solver.WitnessRadix.OpenGraph

/-- The implementation always fills the first remaining hole: zero subtree
first, then the pending right subtrees in stack order. -/
inductive FillFirst (address : BitVec 64) (tree : Graph.Tree) (replacement : Tree) : Tree → Tree → Prop
  | here : FillFirst address tree replacement (.hole address tree) replacement
  | zero {slot node position zero zeroNext one}
      (next : FillFirst address tree replacement zero zeroNext) :
      FillFirst address tree replacement (.branch slot node position zero one) (.branch slot node position zeroNext one)
  | one {slot node position zero one oneNext}
      (closed : frontier zero = []) (next : FillFirst address tree replacement one oneNext) :
      FillFirst address tree replacement (.branch slot node position zero one) (.branch slot node position zero oneNext)

theorem fill_replaces {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : FillFirst address tree replacement before after) : ReplaceHole address tree replacement before after := by
  induction step with
  | here => exact .here
  | zero step ih => exact .zero ih
  | one closed step ih => exact .one ih

/-- A fill removes exactly the active task and prepends the replacement's
children, leaving every pending task in its existing order. -/
theorem fill_frontier {address : BitVec 64} {tree : Graph.Tree} {replacement before after : Tree}
    (step : FillFirst address tree replacement before after) :
    ∃ pending, frontier before = (address, tree) :: pending ∧
      frontier after = frontier replacement ++ pending := by
  induction step with
  | here => exact ⟨[], rfl, by simp⟩
  | @zero slot node position zero zeroNext one step ih =>
      obtain ⟨pending, old, next⟩ := ih
      refine ⟨pending ++ frontier one, ?_, ?_⟩
      · simp only [frontier, old, List.cons_append]
      · simp only [frontier, next, List.append_assoc]
  | @one slot node position zero one oneNext closed step ih =>
      obtain ⟨pending, old, next⟩ := ih
      exact ⟨pending, by simpa only [frontier, closed, List.nil_append] using old,
        by simpa only [frontier, closed, List.nil_append] using next⟩

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.fill_replaces
#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.fill_frontier
