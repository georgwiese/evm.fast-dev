import InitECandidate.Solver.GasBudget.RootEntry
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.Input.WordOperationNormal

namespace InitECandidate.Solver.GasBudget.RootBudget
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A normal run of the real split derives successful scalar reads and the
available call clock, then exposes the exact initialized continuation state.
Only the intrinsic cap and fixed min code remain as entry premises. -/
theorem normal_initialize (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (continuation : ProgHOL 64) (value : ValueHOL 64)
    (capped : RootValidation.CappedIntrinsic source)
    (code : source.code.lookup (ofString "min") = some (Minimum.formals, Minimum.body, .one))
    (run : evaluateHOLFiniteState source (program continuation) = (some (.returned value), post)) :
    ∃ (gas intrinsic regular state floor : BitVec 64) (finish : PanSemStateFiniteExact 64 Guest.HostMemory),
      evaluateHOLFiniteState (entered source gas intrinsic regular) continuation = (some (.returned value), finish) ∧
      (liquidWord gas intrinsic regular).toNat + regular.toNat ≤ 16777216 ∧
      floor.toNat ≤ 16777216 ∧
      source.locals.lookup (ofString "intrinsic") = some (intrinsicValue regular state floor) ∧
      source.locals.lookup (ofString "gas") = some (.val (.word gas)) ∧
      source.locals.lookup (ofString "intrinsic_gas") = some (.val (.word intrinsic)) ∧
      1 ≤ source.clock := by
  have parseRun := run
  unfold program at parseRun
  obtain ⟨execution, firstPost, executionRead, executionShape, firstRun, firstRestore⟩ :=
    Input.CallNormal.declaration_normal_entry source post "execution_gas" .one executionExpression _ value parseRun
  obtain ⟨budget, secondPost, budgetRead, budgetShape, secondRun, secondRestore⟩ :=
    Input.CallNormal.declaration_normal_entry _ firstPost "regular_budget" .one regularExpression _ value firstRun
  have enough := Input.CallNormal.normal_clock _ secondPost (ofString "mgas") .one (ofString "min")
    minArguments (.dec (ofString "reservoir") .one reservoirExpression continuation) value secondRun
  change 1 ≤ source.clock at enough
  obtain ⟨gas, intrinsic, gasLocal, intrinsicLocal⟩ :=
    Input.operation_local_words source "gas" "intrinsic_gas" .sub execution executionRead
  obtain ⟨regular, state, floor, stored, regularCap, floorCap⟩ := capped
  have initialized := execute source gas intrinsic regular state floor gasLocal intrinsicLocal stored code enough continuation
  rw [initialized] at run
  have normal := congrArg Prod.fst run
  exact ⟨gas, intrinsic, regular, state, floor,
    (evaluateHOLFiniteState (entered source gas intrinsic regular) continuation).2,
    Prod.ext normal rfl, liquid_bound gas intrinsic regular regularCap, floorCap,
    stored, gasLocal, intrinsicLocal, enough⟩

end InitECandidate.Solver.GasBudget.RootBudget

#print axioms InitECandidate.Solver.GasBudget.RootBudget.normal_initialize
