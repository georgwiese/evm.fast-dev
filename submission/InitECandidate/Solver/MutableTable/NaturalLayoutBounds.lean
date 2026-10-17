import InitECandidate.Solver.MutableTable.NaturalLayoutFrame

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack

theorem fresh_bounds (kind : KeyHash.Kind) (start capacity : Nat) (pool : Pool) :
    start ≤ (fresh kind start capacity).base pool ∧
      (fresh kind start capacity).base pool + size kind (fresh kind start capacity) pool ≤ freshEnd kind start capacity := by
  cases pool <;> simp only [fresh, size, freshEnd] <;> omega

/-- An earlier or later word lies outside every actual fresh table pool. -/
theorem fresh_cell_away (kind : KeyHash.Kind) (start capacity : Nat) (valid : Valid kind (fresh kind start capacity))
    (query : BitVec 64) (away : query.toNat < start ∨ freshEnd kind start capacity ≤ query.toNat)
    (pool : Pool) (offset : Nat) (inside : offset < size kind (fresh kind start capacity) pool) :
    query ≠ cell (fresh kind start capacity) pool offset := by
  intro same
  have numeric := congrArg BitVec.toNat same
  rw [number kind _ valid pool offset inside] at numeric
  have bounds := fresh_bounds kind start capacity pool
  omega

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.fresh_bounds
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.fresh_cell_away
