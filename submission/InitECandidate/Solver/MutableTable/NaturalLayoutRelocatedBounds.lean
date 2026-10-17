import InitECandidate.Solver.MutableTable.NaturalLayoutBounds

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack

theorem relocated_array_bounds (kind : KeyHash.Kind) (table start capacity : Nat) (pool : Pool) (array : pool ≠ .header) :
    start ≤ (relocated kind table start capacity).base pool ∧
      (relocated kind table start capacity).base pool + size kind (relocated kind table start capacity) pool ≤ relocatedEnd kind start capacity := by
  cases pool <;> simp only [ne_eq, not_true_eq_false] at array <;> simp only [relocated, size, relocatedEnd] <;> omega

theorem relocated_array_away (kind : KeyHash.Kind) (table start capacity : Nat) (valid : Valid kind (relocated kind table start capacity))
    (address : BitVec 64) (away : address.toNat < start ∨ relocatedEnd kind start capacity ≤ address.toNat)
    (pool : Pool) (array : pool ≠ .header) (offset : Nat) (inside : offset < size kind (relocated kind table start capacity) pool) :
    address ≠ cell (relocated kind table start capacity) pool offset := by
  intro equal
  have numeric := congrArg BitVec.toNat equal
  rw [number kind _ valid pool offset inside] at numeric
  have bounds := relocated_array_bounds kind table start capacity pool array
  omega

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.relocated_array_bounds
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.relocated_array_away
