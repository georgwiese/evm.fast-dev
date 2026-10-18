import InitECandidate.Solver.GasBudget.WarmKeysStep

namespace InitECandidate.Solver.GasBudget.WarmKeys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

def price (count remaining : Nat) : Nat := (13 * count + 17) * remaining + 13 * WitnessBuild.triangle remaining

theorem price_step (count remaining : Nat) : price count (remaining + 1) = 13 * count + 17 + price (count + 1) remaining := by
  simp only [price, WitnessBuild.triangle, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
  omega

theorem price_mono (first second remaining : Nat) (bounded : first ≤ second) : price first remaining ≤ price second remaining := by
  have bound := Nat.mul_le_mul_right remaining (show 13 * first + 17 ≤ 13 * second + 17 from by omega)
  exact Nat.add_le_add_right bound _

/-- Whole original storage-key warm-up loop on a covered normal execution.
The iteration count follows from its actual signed counter and input extent.
Every reached setter establishes the next physical model and allocation room;
there is no supplied event trace, clock budget or future-growth oracle. -/
theorem loop_normal (remaining : Nat) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start total index floor cursor : Nat) (plan : Plan) (slots : List Nat)
    (inputValid : MemoryRegion.Valid (inputRegion start total)) (count : index + remaining = total)
    (environment : Environment source) (table : Table source plan slots cursor floor)
    (locals : Locals source (cell plan .header 0) start total index)
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor,
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .storage plan.capacity ≤ price slots.length remaining + GrowRuntime.growthPotential .storage nextPlan.capacity ∧
      Table target nextPlan nextSlots nextCursor floor ∧ Environment target ∧
      Locals target (cell nextPlan .header 0) start total total ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + remaining ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (slots.length + remaining + 1)) ∧
      HeapGlobals source target ∧
      ∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address := by
  induction remaining generalizing source index plan slots cursor with
  | zero =>
    have finished : index = total := by omega
    have test := condition_read source _ start total index inputValid (by omega) locals
    rw [if_neg (by omega)] at test
    have actual : evaluateHOLFiniteState source loop = (none, source) := by
      simp only [eval, evalHOLFinite] at test
      rw [loop, evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite, test]
      simp
    have same := congrArg Prod.snd (normal.symm.trans actual)
    change target = source at same
    subst target
    refine ⟨0, plan, slots, cursor, by omega, by simp, by simp [price, WitnessBuild.triangle], table, environment,
      by simpa only [finished] using locals, by omega, by omega, Nat.le_max_left _ _, HeapGlobals.refl _, ?_⟩
    intro address earlier
    rfl
  | succ remaining ih =>
    have active : index < total := by omega
    have test := condition_read source _ start total index inputValid (by omega) locals
    rw [if_pos active] at test
    obtain ⟨positive, middle, bodyRun, tailRun, clockBound⟩ :=
      Input.while_none_step source target (ofString "nkeys") condition loopBody body_safe test normal
    let entry := decClockHOLFinite source
    have entryEnvironment : Environment entry := environment.of_fields rfl rfl rfl
    have entryTable : Table entry plan slots cursor floor := table.of_fields rfl rfl rfl rfl
    have entryLocals : Locals entry (cell plan .header 0) start total index := locals.of_locals rfl
    obtain ⟨paid, middlePlan, middleSlots, middleCursor, fits, clockEq, localBound, middleTable, middleEnvironment,
      middleLocals, lower, upper, middleCapacity, middleGlobals, middleProtected⟩ :=
      body_normal entry middle start total index floor cursor plan slots inputValid active entryEnvironment entryTable entryLocals bodyRun
    obtain ⟨restPaid, finalPlan, finalSlots, finalCursor, restFits, restClock, restBound, finalTable, finalEnvironment,
      finalLocals, finalLower, finalUpper, finalCapacity, finalGlobals, finalProtected⟩ :=
      ih (source := middle) (index := index + 1) (cursor := middleCursor) (plan := middlePlan) (slots := middleSlots) (by omega)
        middleEnvironment middleTable middleLocals tailRun
    change paid ≤ source.clock - 1 at fits
    change middle.clock = source.clock - 1 - paid at clockEq
    have monotone := price_mono middleSlots.length (slots.length + 1) remaining upper
    have totalBound : 1 + paid + restPaid + GrowRuntime.growthPotential .storage plan.capacity ≤
        price slots.length (remaining + 1) + GrowRuntime.growthPotential .storage finalPlan.capacity := by
      rw [price_step]
      omega
    refine ⟨1 + paid + restPaid, finalPlan, finalSlots, finalCursor, by omega, by omega, totalBound,
      finalTable, finalEnvironment, finalLocals, by omega, by omega, ?_, middleGlobals.trans finalGlobals, ?_⟩
    · omega
    · intro address earlier
      exact (finalProtected address earlier).trans (middleProtected address earlier)

end InitECandidate.Solver.GasBudget.WarmKeys

#print axioms InitECandidate.Solver.GasBudget.WarmKeys.price_step
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.price_mono
#print axioms InitECandidate.Solver.GasBudget.WarmKeys.loop_normal
