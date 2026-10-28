import Mathlib.Order.Monotone.Basic
import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega

namespace InitECandidate.Solver.Input.Progressive

/-- Actual cumulative chunks skipped by the original sizes1,4,16,... . -/
def offset : Nat→Nat | 0=>0 | k+1=>offset k+4^k

theorem offset_mono : Monotone offset := by
  apply monotone_nat_of_le_succ
  intro k
  change offset k≤offset k+4^k
  exact Nat.le_add_right _ _

/-- Even the conservative whole-input chunk ceiling needs at most15
original progressive rounds, fitting the original24-root allocation. -/
theorem active_round (n k : Nat) (bounded : n≤134217728) (active : offset k<n) : k<15 := by
  by_cases round : k < 15
  · exact round
  have lower := offset_mono (show 15≤k by omega)
  have exactOffset : offset 15=357913941 := by decide
  rw [exactOffset] at lower
  omega

theorem round_geometry (n k : Nat) (bounded : n≤134217728) (active : offset k<n) :
    k<15 ∧ 2*k<64 ∧ 4^k=2^(2*k) ∧ 4^k≤268435456 ∧ min (4^k) (n-offset k)>0 := by
  have kBound := active_round n k bounded active
  have positive : 0<4^k := Nat.pow_pos (by decide)
  have power : 4^k=2^(2*k) := by rw [Nat.pow_mul]
  have upper : 4^k≤4^14 := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨kBound,by omega,power,?_,by omega⟩
  exact upper

/-- Remaining source-clock allowance for the actual progressive loop.
A round pays for its actual nonempty chunks plus its bounded depth work. -/
def allowance (n off k : Nat) := 115*(n-off)+1555*(15-k)

theorem amortized_round (n off size k : Nat) (active : off<n) (positive : 0<size) (round : k<15) :
    115*min size (n-off)+1555+allowance n (off+size) (k+1)≤allowance n off k := by
  unfold allowance
  by_cases inside : size≤n-off
  · rw [Nat.min_eq_left inside]
    omega
  · rw [Nat.min_eq_right (by omega : n-off≤size)]
    omega

/-- Actual original per-call depth price fits the round overhead. -/
theorem round_price (k : Nat) (round : k<15) : 55*(2*k)+14+1≤1555 := by omega

/-- Current software Merkle costs: linear chunks plus at most200ticks per
actual geometric round, with at most15rounds from the real count ceiling. -/
def currentAllowance (n off k : Nat) := 88*(n-off)+200*(15-k)

theorem current_amortized_round (n off size k : Nat) (active : off<n) (positive : 0<size) (round : k<15) :
    88*min size (n-off)+200+currentAllowance n (off+size) (k+1)≤currentAllowance n off k := by
  unfold currentAllowance
  by_cases inside : size≤n-off
  · rw [Nat.min_eq_left inside]; omega
  · rw [Nat.min_eq_right (by omega : n-off≤size)]; omega

theorem current_round_price (k : Nat) (round : k<15) : 4*(2*k)+49+1≤200 := by omega

end InitECandidate.Solver.Input.Progressive

#print axioms InitECandidate.Solver.Input.Progressive.offset_mono
#print axioms InitECandidate.Solver.Input.Progressive.active_round
#print axioms InitECandidate.Solver.Input.Progressive.round_geometry
#print axioms InitECandidate.Solver.Input.Progressive.amortized_round
#print axioms InitECandidate.Solver.Input.Progressive.round_price

#print axioms InitECandidate.Solver.Input.Progressive.current_amortized_round
#print axioms InitECandidate.Solver.Input.Progressive.current_round_price
