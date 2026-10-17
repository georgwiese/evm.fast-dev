import InitECandidate.Solver.MutableTable.NaturalLayoutFresh

namespace InitECandidate.Solver.MutableTable.NaturalLayout
open Flapjack

def relocated (kind : KeyHash.Kind) (table start capacity : Nat) : Plan where
  capacity := capacity
  base := fun pool => match pool with
    | .header => table
    | .keys => start
    | .values => start + stride kind * capacity
    | .used => start + stride kind * capacity + 8 * capacity
    | .order => start + stride kind * capacity + 8 * capacity + rounded capacity
    | .position => start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity

def relocatedEnd (kind : KeyHash.Kind) (start capacity : Nat) : Nat :=
  start + stride kind * capacity + 8 * capacity + rounded capacity + 8 * capacity + 8 * capacity

/-- The five actual growth allocations preserve a separate prior header.
Both a persistent header below the new arrays and a scratch header above
them are permitted. This proves geometry, not allocation reachability. -/
theorem relocated_valid (kind : KeyHash.Kind) (table start capacity : Nat) (positive : 0 < capacity)
    (tableLower : 2701131776 ≤ table) (startLower : 2701131776 ≤ start)
    (tableFits : table + 72 ≤ 33806089496) (fits : relocatedEnd kind start capacity ≤ 33806089496)
    (tableAligned : table % 8 = 0) (startAligned : start % 8 = 0)
    (separated : table + 72 ≤ start ∨ relocatedEnd kind start capacity ≤ table) :
    Valid kind (relocated kind table start capacity) := by
  have strideAligned := (stride_bounds kind).2.2
  have usedAligned := (rounded_bounds capacity).2.2
  refine ⟨positive, ?_, ?_, ?_, ?_⟩
  · intro pool
    cases pool <;> simp only [relocated] <;> omega
  · intro pool
    cases pool <;> simp only [relocated, size] <;> dsimp only [relocatedEnd] at fits <;> omega
  · intro pool
    cases pool <;> simp [relocated, Nat.add_mod, Nat.mul_mod, tableAligned, startAligned, strideAligned, usedAligned]
  · intro first second different
    cases first <;> cases second <;> simp only [ne_eq, not_true_eq_false] at different <;>
      simp only [relocated, size] <;> dsimp only [relocatedEnd] at separated <;> omega

/-- The natural slot stride matches the unchanged constructor's exact word
expression at all five original key widths. -/
theorem stride_word (kind : KeyHash.Kind) :
    (BitVec.ofNat 64 (KeyHash.keySize kind) + 7#64) &&& (0#64 - 8#64) = BitVec.ofNat 64 (stride kind) := by
  cases kind <;> decide

end InitECandidate.Solver.MutableTable.NaturalLayout

#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.relocated_valid
#print axioms InitECandidate.Solver.MutableTable.NaturalLayout.stride_word
