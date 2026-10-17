import InitECandidate.Solver.WitnessRadix.OpenGraphFrontier

namespace InitECandidate.Solver.WitnessRadix.OpenGraph

/-- Any nonempty frontier has an actual first-hole replacement. This supplies
the graph transition used by the loop invariant, rather than assuming it. -/
theorem fill_first_exists (before : Tree) (address : BitVec 64) (expected : Graph.Tree) (replacement : Tree)
    (pending : List (BitVec 64 × Graph.Tree)) (head : frontier before = (address, expected) :: pending) :
    ∃ after, FillFirst address expected replacement before after := by
  induction before generalizing pending with
  | hole slot tree =>
      have same : slot = address ∧ tree = expected := by
        have pair := (List.cons.inj head).1
        exact Prod.mk.inj pair
      obtain ⟨rfl, rfl⟩ := same
      exact ⟨replacement, .here⟩
  | complete slot root tree => simp [frontier] at head
  | branch slot node position zero one ihZero ihOne =>
      cases first : frontier zero with
      | nil =>
          have rightHead : frontier one = (address, expected) :: pending := by
            simpa only [frontier, first, List.nil_append] using head
          obtain ⟨oneNext, next⟩ := ihOne pending rightHead
          exact ⟨.branch slot node position zero oneNext, .one first next⟩
      | cons entry rest =>
          have same : entry = (address, expected) := by
            have joined : entry :: (rest ++ frontier one) = (address, expected) :: pending := by
              simpa only [frontier, first, List.cons_append] using head
            exact (List.cons.inj joined).1
          have zeroHead : frontier zero = (address, expected) :: rest := first.trans (by rw [same])
          obtain ⟨zeroNext, next⟩ := ihZero rest zeroHead
          exact ⟨.branch slot node position zeroNext one, .zero next⟩

end InitECandidate.Solver.WitnessRadix.OpenGraph

#print axioms InitECandidate.Solver.WitnessRadix.OpenGraph.fill_first_exists
