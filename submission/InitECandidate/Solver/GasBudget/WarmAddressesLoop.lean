import InitECandidate.Solver.GasBudget.WarmAddressesStep
import InitECandidate.Solver.GasBudget.WarmPrecompilesLoop

namespace InitECandidate.Solver.GasBudget.WarmAddresses
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch MutableTable NaturalLayout

abbrev price := WarmPrecompiles.price

/-- Whole original access-list address warming loop on a covered normal execution.
The iteration count follows from its actual signed counter and input extent.
Each query is the actual load from the protected pointer array.
Every reached setter establishes the next physical model and allocation room;
there is no supplied event trace, clock budget or future-growth oracle. -/
theorem loop_normal (remaining : Nat) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (start count index floor cursor : Nat) (plan : Plan) (slots : List Nat) (pointers : Nat → BitVec 64)
    (array : PointerArray source.memory 20 start count floor pointers) (positive : 0 < count) (extent : index + remaining = count)
    (environment : WarmKeys.Environment source) (table : TableState source .account plan slots cursor floor)
    (locals : Locals source (cell plan .header 0) start count index)
    (normal : evaluateHOLFiniteState source loop = (none, target)) :
    ∃ paid nextPlan nextSlots nextCursor,
      paid ≤ source.clock ∧ target.clock = source.clock - paid ∧
      paid + GrowRuntime.growthPotential .account plan.capacity ≤ price slots.length remaining + GrowRuntime.growthPotential .account nextPlan.capacity ∧
      TableState target .account nextPlan nextSlots nextCursor floor ∧ WarmKeys.Environment target ∧
      PointerArray target.memory 20 start count floor pointers ∧
      Locals target (cell nextPlan .header 0) start count count ∧
      slots.length ≤ nextSlots.length ∧ nextSlots.length ≤ slots.length + remaining ∧
      nextPlan.capacity ≤ max plan.capacity (4 * (slots.length + remaining + 1)) ∧
      ∀ address : BitVec 64, address.toNat < floor → target.memory address = source.memory address := by
  induction remaining generalizing source index plan slots cursor with
  | zero =>
    have finished : index = count := by omega
    have test := condition_read source _ start count index array.valid positive (by omega) locals
    rw [if_neg (by omega)] at test
    have actual : evaluateHOLFiniteState source loop = (none, source) := by
      simp only [eval, evalHOLFinite] at test
      rw [loop, evaluateHOLFiniteState_while_total]
      simp only [evalHOLFinite, test]
      simp
    have same := congrArg Prod.snd (normal.symm.trans actual)
    change target = source at same
    subst target
    refine ⟨0, plan, slots, cursor, by omega, by simp, by simp [price, WarmPrecompiles.price, WitnessBuild.triangle], table, environment, array,
      by simpa only [finished] using locals, by omega, by omega, Nat.le_max_left _ _, ?_⟩
    intro address earlier
    rfl
  | succ remaining ih =>
    have active : index < count := by omega
    have test := condition_read source _ start count index array.valid positive (by omega) locals
    rw [if_pos active] at test
    obtain ⟨positive, middle, bodyRun, tailRun, clockBound⟩ :=
      Input.while_none_step source target (ofString "m") condition loopBody body_safe test normal
    let entry := decClockHOLFinite source
    have entryEnvironment : WarmKeys.Environment entry := environment.of_fields rfl rfl rfl
    have entryTable : TableState entry .account plan slots cursor floor := table.of_fields rfl rfl rfl rfl
    have entryLocals : Locals entry (cell plan .header 0) start count index := locals.of_locals rfl
    obtain ⟨paid, middlePlan, middleSlots, middleCursor, fits, clockEq, localBound, middleTable, middleEnvironment,
      middleArray, middleLocals, lower, upper, middleCapacity, middleProtected⟩ :=
      body_normal entry middle start count index floor cursor plan slots pointers array active entryEnvironment entryTable entryLocals bodyRun
    obtain ⟨restPaid, finalPlan, finalSlots, finalCursor, restFits, restClock, restBound, finalTable, finalEnvironment,
      finalArray, finalLocals, finalLower, finalUpper, finalCapacity, finalProtected⟩ :=
      ih (source := middle) (index := index + 1) (cursor := middleCursor) (plan := middlePlan) (slots := middleSlots) middleArray (by omega)
        middleEnvironment middleTable middleLocals tailRun
    change paid ≤ source.clock - 1 at fits
    change middle.clock = source.clock - 1 - paid at clockEq
    have monotone := WarmPrecompiles.price_mono middleSlots.length (slots.length + 1) remaining upper
    have totalBound : 1 + paid + restPaid + GrowRuntime.growthPotential .account plan.capacity ≤
        price slots.length (remaining + 1) + GrowRuntime.growthPotential .account finalPlan.capacity := by
      dsimp only [price] at restBound ⊢
      rw [WarmPrecompiles.price_step]
      omega
    refine ⟨1 + paid + restPaid, finalPlan, finalSlots, finalCursor, by omega, by omega, totalBound,
      finalTable, finalEnvironment, finalArray, finalLocals, by omega, by omega, ?_, ?_⟩
    · omega
    · intro address earlier
      exact (finalProtected address earlier).trans (middleProtected address earlier)

end InitECandidate.Solver.GasBudget.WarmAddresses

#print axioms InitECandidate.Solver.GasBudget.WarmAddresses.loop_normal
