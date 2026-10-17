import InitECandidate.Solver.WitnessRadix.CapacityLoop

namespace InitECandidate.Solver.WitnessRadix.Capacity
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual doubling loop terminates at a sufficient power of two,
preserves all nonlocal fields and other locals, and pays at most fuel clocks. -/
theorem iterate_exact {F : Type} (source : PanSemStateFiniteExact 64 F) (count exponent fuel : Nat)
    (small : count < 2 ^ 31) (lowerExp : 2 ≤ exponent) (top : exponent + fuel ≤ 32)
    (capBound : 2 ^ exponent ≤ 4 * count + 4) (dominates : 2 * count + 2 ≤ 2 ^ (exponent + fuel))
    (countLocal : source.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))))
    (capLocal : source.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ exponent)))))
    (enough : fuel ≤ source.clock) :
    ∃ target : PanSemStateFiniteExact 64 F, ∃ paid finalExp : Nat,
      evaluateHOLFiniteState source Constructor.capacityLoop = (none, target) ∧ paid ≤ fuel ∧
      exponent ≤ finalExp ∧ finalExp ≤ exponent + fuel ∧ 2 * count + 2 ≤ 2 ^ finalExp ∧
      2 ^ finalExp ≤ 4 * count + 4 ∧
      target.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ finalExp)))) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with clock := source.clock - paid } ∧
      (∀ name : MlS, ofString "cap" ≠ name → target.locals.lookup name = source.locals.lookup name) ∧
      finalExp=exponent+paid ∧ (2^finalExp<4*count+4 ∨ finalExp=exponent) := by
  classical
  induction fuel generalizing source exponent with
  | zero =>
    have inactive : ¬ 2 ^ exponent < 2 * count + 2 := by simpa only [Nat.add_zero] using Nat.not_lt.mpr dominates
    refine ⟨source, 0, exponent, skip_loop source count exponent small (by omega) countLocal capLocal inactive,
      Nat.le_refl _, Nat.le_refl _, by omega, by simpa only [Nat.add_zero] using dominates, capBound, capLocal, ?_, ?_,by omega,Or.inr rfl⟩
    · simp
    · intro name _; rfl
  | succ fuel ih =>
    by_cases active : 2 ^ exponent < 2 * count + 2
    · have positive : source.clock ≠ 0 := by omega
      let entry := decClockHOLFinite source
      let next := bind entry "cap" (BitVec.ofNat 64 (2 ^ (exponent + 1)))
      have bodyRun : evaluateHOLFiniteState (decClockHOLFinite source) step = (none, next) :=
        step_execute entry exponent capLocal
      have nextCap : next.locals.lookup (ofString "cap") = some (.val (.word (BitVec.ofNat 64 (2 ^ (exponent + 1))))) :=
        bind_lookup_same _ _ _
      have nextOther (name : MlS) (different : ofString "cap" ≠ name) : next.locals.lookup name = source.locals.lookup name := by
        simp [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, HolFiniteMapExact.update, FUPDATE, different]
      have nextCount : next.locals.lookup (ofString "n") = some (.val (.word (BitVec.ofNat 64 count))) :=
        (nextOther _ (by decide)).trans countLocal
      have nextCapBound : 2 ^ (exponent + 1) ≤ 4 * count + 4 := by rw [Nat.pow_succ]; omega
      have nextDominates : 2 * count + 2 ≤ 2 ^ (exponent + 1 + fuel) := by
        have total : exponent + 1 + fuel = exponent + (fuel + 1) := by omega
        rw [total]; exact dominates
      obtain ⟨target, paid, finalExp, run, budget, low, high, sufficient, capUpper, finalCap, frame, others,expPaid,minimal⟩ :=
        ih next (exponent + 1) (by omega) (by omega) nextCapBound nextDominates nextCount nextCap
          (by change fuel ≤ source.clock - 1; omega)
      have clockEq : source.clock - 1 - paid = source.clock - (paid + 1) := by omega
      have totalFrame : emptyLocalsHOLFinite target = emptyLocalsHOLFinite { source with clock := source.clock - (paid + 1) } := by
        rw [frame]
        simp only [next, entry, QueryBranch.bind, setVarHOLFinite, decClockHOLFinite, emptyLocalsHOLFinite, clockEq]
      refine ⟨target, paid + 1, finalExp, ?_, by omega, by omega, by omega, sufficient, capUpper, finalCap, totalFrame, ?_,by omega,?minimal⟩
      case minimal =>
        rcases minimal with strict | same
        · exact Or.inl strict
        · apply Or.inl
          rw [same,Nat.pow_succ]
          omega
      · rw [loop_shape, evaluateHOLFiniteState_while_total, condition_read source count exponent small (by omega) countLocal capLocal]
        simp only [if_pos active]
        rw [if_pos (show (1#64 : BitVec 64) ≠ (0 : BitVec 64) from by decide)]
        simp only [if_neg positive]
        rw [bodyRun, StateSteps.fixed_clock entry next none (Nat.le_refl _)]
        change evaluateHOLFiniteState next (.while condition step) = _
        rw [← loop_shape]
        exact run
      · intro name different
        exact (others name different).trans (nextOther name different)
    · refine ⟨source, 0, exponent, skip_loop source count exponent small (by omega) countLocal capLocal active,
        by omega, Nat.le_refl _, by omega, by omega, capBound, capLocal, ?_, ?_,by omega,Or.inr rfl⟩
      · simp
      · intro name _; rfl

end InitECandidate.Solver.WitnessRadix.Capacity

#print axioms InitECandidate.Solver.WitnessRadix.Capacity.iterate_exact
