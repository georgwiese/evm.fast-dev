import InitECandidate.Solver.MutableTable.NaturalLayout

namespace InitECandidate.Solver.MutableTable.NaturalLayout

def fresh (kind : KeyHash.Kind) (start capacity : Nat) : Plan where
  capacity := capacity
  base := fun pool => match pool with
    | .header => start
    | .keys => start + 72
    | .values => start + 72 + stride kind * capacity
    | .used => start + 72 + stride kind * capacity + 8 * capacity
    | .order => start + 72 + stride kind * capacity + 8 * capacity + rounded capacity
    | .position => start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity

def freshEnd (kind : KeyHash.Kind) (start capacity : Nat) : Nat :=
  start + 72 + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity + 8 * capacity

/-- The actual allocation order of a new table derives all pool ownership,
alignment, no-wrap and separation facts, including short used-array padding.
Allocator reachability/available room still supply start and the end bound. -/
theorem fresh_valid (kind : KeyHash.Kind) (start capacity : Nat) (positive : 0 < capacity)
    (lower : 2701131776 ≤ start) (fits : freshEnd kind start capacity ≤ 33806089496) (aligned : start % 8 = 0) :
    Valid kind (fresh kind start capacity) := by
  have strideAligned := (stride_bounds kind).2.2
  have usedAligned := (rounded_bounds capacity).2.2
  refine ⟨positive, ?_, ?_, ?_, ?_⟩
  · intro pool
    cases pool <;> simp only [fresh] <;> omega
  · intro pool
    cases pool <;> simp only [fresh, size] <;> dsimp only [freshEnd] at fits <;> omega
  · intro pool
    cases pool <;> simp [fresh, Nat.add_mod, Nat.mul_mod, aligned, strideAligned, usedAligned]
  · intro first second different
    cases first <;> cases second <;> simp only [ne_eq, not_true_eq_false] at different <;>
      simp only [fresh, size] <;> omega

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.fresh_valid
