import InitE.NatE

/-! Small clock-accounting lemmas. These do not assume a compiler cost bound
or assert a finite certificate. Instantiating them requires actual run bounds. -/
namespace InitECandidate.Solver.ClockBounds

/-- A known quiet-prefix clock shift adds its cost to a terminating budget. -/
theorem prefix_within {α : Type} (before after : Nat → α) (result : α)
    (prefixCost budget : Nat)
    (shift : ∀ clock, before (prefixCost + clock) = after clock)
    (run : ∃ clock, clock ≤ budget ∧ after clock = result) :
    ∃ clock, clock ≤ prefixCost + budget ∧ before clock = result := by
  obtain ⟨clock, bound, execution⟩ := run
  exact ⟨prefixCost + clock, Nat.add_le_add_left bound prefixCost,
    (shift clock).trans execution⟩

/-- Quantitative simulation transports a finite budget through a monotone map. -/
theorem transport_within (source target : Nat → Prop) (cost : Nat → Nat)
    (monotone : ∀ a b, a ≤ b → cost a ≤ cost b)
    (simulate : ∀ clock, source clock →
      ∃ used, used ≤ cost clock ∧ target used)
    {budget : Nat} (run : InitE.NatE.Within (.finite budget) source) :
    InitE.NatE.Within (.finite (cost budget)) target := by
  obtain ⟨clock, bound, execution⟩ := run
  obtain ⟨used, usedBound, targetRun⟩ := simulate clock execution
  exact ⟨used, Nat.le_trans usedBound (monotone clock budget bound), targetRun⟩

/-- Finitely many terminating cases have a common finite budget. This gives
no numeric ceiling and cannot establish the Yukon score cap by itself. -/
theorem finite_family_bound {α : Type} (cases : List α) (run : α → Nat → Prop)
    (terminates : ∀ input ∈ cases, ∃ clock, run input clock) :
    ∃ budget, ∀ input ∈ cases, InitE.NatE.Within (.finite budget) (run input) := by
  induction cases with
  | nil => exact ⟨0, by simp⟩
  | cons head tail ih =>
    obtain ⟨clock, execution⟩ := terminates head (by simp)
    obtain ⟨budget, bounded⟩ := ih (fun input member =>
      terminates input (List.mem_cons_of_mem head member))
    refine ⟨max clock budget, ?_⟩
    intro input member
    rcases List.mem_cons.mp member with eq | member
    · subst input
      exact ⟨clock, Nat.le_max_left _ _, execution⟩
    · obtain ⟨used, bound, execution⟩ := bounded input member
      exact ⟨used, Nat.le_trans bound (Nat.le_max_right _ _), execution⟩

end InitECandidate.Solver.ClockBounds

#print axioms InitECandidate.Solver.ClockBounds.prefix_within
#print axioms InitECandidate.Solver.ClockBounds.transport_within
#print axioms InitECandidate.Solver.ClockBounds.finite_family_bound
