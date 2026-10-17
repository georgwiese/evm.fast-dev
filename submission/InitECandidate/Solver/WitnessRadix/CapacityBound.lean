import InitECandidate.Solver.WitnessRadix.CapacityLoop

namespace InitECandidate.Solver.WitnessRadix.Capacity
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem count_small_of_records (records table count : Nat)
    (lower : 2701131776 ≤ records) (beforeTable : records + 16 * count ≤ table)
    (upper : table ≤ 33806089496) : count < 2 ^ 31 := by omega

theorem power_shape (exponent : Nat) (lower : 2 ≤ exponent) : 2 ^ exponent = 4 ∨ (2 ^ exponent) % 8 = 0 := by
  by_cases two : exponent = 2
  · subst exponent; exact Or.inl rfl
  · have three : 3 ≤ exponent := by omega
    have divides : 8 ∣ 2 ^ exponent := Nat.pow_dvd_pow 2 three
    exact Or.inr (Nat.mod_eq_zero_of_dvd divides)

/-- The actual initial cap=4 loop uses at most thirty source clocks, chooses
a sufficient power of two at most 4*N+4, and changes no other live data. -/
theorem bounded {F : Type} (source : PanSemStateFiniteExact 64 F) (count : Nat) (small : count < 2 ^ 31)
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word 4#64))) (enough : 30 ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ paid capacity : Nat,
      evaluateHOLFiniteState source Constructor.capacityLoop = (none, target) ∧ paid ≤ 30 ∧
      2 * count + 2 ≤ capacity ∧ capacity ≤ 4 * count + 4 ∧ capacity ≤ 2 ^ 32 ∧
      (capacity = 4 ∨ capacity % 8 = 0) ∧
      target.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 capacity))) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with clock := source.clock - paid } ∧
      (∀ name : MlS, ofString "cap" ≠ name → target.locals.lookup name = source.locals.lookup name) := by
  obtain ⟨target, paid, exponent, run, budget, lower, upper, sufficient, capUpper, cap, frame, others⟩ :=
    iterate source count 2 30 small (by decide) (by decide) (by omega) (by omega) countLocal capLocal enough
  refine ⟨target, paid, 2 ^ exponent, run, budget, sufficient, capUpper, ?_, power_shape exponent lower, cap, frame, others⟩
  exact Nat.pow_le_pow_right (by decide) upper

end InitECandidate.Solver.WitnessRadix.Capacity

#print axioms InitECandidate.Solver.WitnessRadix.Capacity.count_small_of_records
#print axioms InitECandidate.Solver.WitnessRadix.Capacity.bounded
