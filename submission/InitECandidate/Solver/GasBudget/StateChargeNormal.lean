import InitECandidate.Solver.GasBudget.StateChargeSaturated
import InitECandidate.Solver.Input.NormalCallClock
import InitECandidate.Solver.Input.PureGuardNormal
import InitECandidate.Solver.ClockPadding

namespace InitECandidate.Solver.GasBudget.StateCharge
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The two actual charge guards derive affordability on a normal return.
This requires neither a fitting combined-pool sum, a clock allowance nor a
valid exception-shape premise. Unaffordable execution cannot pass its raise. -/
theorem normal_affordable (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill)
    (amountLocal : source.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) : amount.toNat ≤ state.toNat + gas.toNat := by
  by_contra unavailable
  have unaffordable : state.toNat + gas.toNat < amount.toNat := by omega
  have fits : state.toNat + gas.toNat < 2 ^ 64 := by have small := amount.isLt; omega
  have stateRead := frame_read source frame 72#64 state pools.ev (pools.mapped 72 (by simp)) pools.state
  let ss := bind source "sgl" state
  have gasRead := frame_read ss frame 64#64 gas pools.ev (pools.mapped 64 (by simp)) pools.gas
  let entered := bind ss "gl" gas
  have setup : WitnessRadix.BuildEntry.Initializes source bindings entered
      (fun output => restore source "sgl" (restore ss "gl" output)) := .step _ stateRead (.step _ gasRead (.done _))
  have stateE : entered.locals.lookup (ofString "sgl") = some (.val (.word state)) :=
    (bind_lookup_other _ "gl" "sgl" _ (by decide)).trans (bind_lookup_same _ _ _)
  have gasE : entered.locals.lookup (ofString "gl") = some (.val (.word gas)) := bind_lookup_same _ _ _
  have amountE : entered.locals.lookup (ofString "amount") = some (.val (.word amount)) :=
    (bind_lookup_other _ "gl" "amount" _ (by decide)).trans ((bind_lookup_other _ "sgl" "amount" _ (by decide)).trans amountLocal)
  have reservoirTooSmall : state < amount := by change state.toNat < amount.toNat; omega
  have firstRun : evaluateHOLFiniteState entered (.ite firstTest firstBranch .skip) = (none, entered) := by
    rw [evaluateHOLFiniteState_ite]
    simp [firstTest, evalHOLExact, toExact, localVar, stateE, amountE, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, reservoirTooSmall]
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [localVar "sgl", localVar "gl"] =
      some [.val (.word state), .val (.word gas)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, stateE, gasE]
  have expanded := normal
  rw [body_shape, WitnessRadix.BuildEntry.declarations_execute setup afterPools] at expanded
  let enteredPost := (evaluateHOLFiniteState entered afterPools).2
  have enteredResult := congrArg Prod.fst expanded
  change (evaluateHOLFiniteState entered afterPools).1 = some (.returned value) at enteredResult
  have enteredRun : evaluateHOLFiniteState entered afterPools = (some (.returned value), enteredPost) := Prod.ext enteredResult rfl
  rw [afterPools, WitnessRadix.StateSteps.next_sequence entered entered _ _ firstRun (Nat.le_refl _)] at enteredRun
  have enough := Input.CallNormal.normal_clock entered enteredPost (ofString "tot") .one (ofString "add_sat") _ afterTotal value enteredRun
  have addRun := AddExact.call_execute entered state gas "tot" [localVar "sgl", localVar "gl"] afterTotal args addCode fits enough
  rw [addRun] at enteredRun
  let st := bind {entered with clock := entered.clock - 1} "tot" (state + gas)
  let totalPost := (evaluateHOLFiniteState st afterTotal).2
  have totalResult := congrArg Prod.fst enteredRun
  change (evaluateHOLFiniteState st afterTotal).1 = some (.returned value) at totalResult
  have totalRun : evaluateHOLFiniteState st afterTotal = (some (.returned value), totalPost) := Prod.ext totalResult rfl
  have totalT : st.locals.lookup (ofString "tot") = some (.val (.word (state + gas))) := bind_lookup_same _ _ _
  have amountT : st.locals.lookup (ofString "amount") = some (.val (.word amount)) := (bind_lookup_other _ "tot" "amount" _ (by decide)).trans amountE
  have sumTooSmall : state + gas < amount := by change (state + gas).toNat < amount.toNat; rw [BitVec.toNat_add_of_lt fits]; exact unaffordable
  have secondRun : evaluateHOLFiniteState st (.ite totalTest spillCode .skip) = (none, st) := by
    rw [evaluateHOLFiniteState_ite]
    simp [totalTest, evalHOLExact, toExact, localVar, totalT, amountT, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sumTooSmall]
  rw [afterTotal, WitnessRadix.StateSteps.next_sequence st st _ _ secondRun (Nat.le_refl _)] at totalRun
  have raisedPassed := (Input.PureGuard.raise (ofString "EvmErr") (.const 4#64)).normal_passed st totalPost returnZero value totalRun
  exact Input.raise_ne_none st (ofString "EvmErr") (.const 4#64) (congrArg Prod.fst raisedPassed)

/-- Bound the actual original state charge, including saturating overflow,
and strip temporary funding. Price0 is a reservoir-only body, price1 a body
that executes add_sat. Actual allocations or helper results are not premises. -/
theorem body_bound (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (frame gas state spill amount : BitVec 64)
    (pools : Pools source frame gas state spill)
    (amountLocal : source.locals.lookup (ofString "amount") = some (.val (.word amount)))
    (addCode : source.code.lookup (ofString "add_sat") = some (AddExact.formals, AddExact.body, .one))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), target)) :
    ∃ paid, paid ≤ 1 ∧ paid ≤ source.clock ∧ amount.toNat ≤ state.toNat + gas.toNat ∧ value = .val (.word 0#64) ∧
      target.memory = WitnessRadix.WordWrites.write source.memory (poolWrites frame gas state spill amount) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := target.memory, clock := source.clock - paid} := by
  have affordable := normal_affordable source target frame gas state spill amount pools amountLocal addCode value normal
  let padded := {source with clock := source.clock + 1}
  have paddedPools : Pools padded frame gas state spill := ⟨pools.ev, pools.mapped, pools.gas, pools.state, pools.spill⟩
  obtain ⟨checked, paid, bound, actual, memory, frame⟩ := execute_saturated padded frame gas state spill amount paddedPools amountLocal addCode affordable (by change 1 ≤ source.clock + 1; omega)
  have lifted := panPropsEvaluateAddClockEq body source (some (.returned value)) target 1 ⟨normal, by intro impossible; cases impossible⟩
  have resultEq := congrArg Prod.fst (lifted.symm.trans actual)
  have valueEq : value = .val (.word 0#64) := by simpa only [Option.some.injEq, PanSemResultExact.returned.injEq] using resultEq
  have targetEq := congrArg Prod.snd (lifted.symm.trans actual)
  change {target with clock := target.clock + 1} = checked at targetEq
  rw [← targetEq] at frame memory
  have stripped := InitECandidate.Solver.strip_clock_padding source target {source with memory := target.memory} paid 1 (by omega) frame
  exact ⟨paid, bound, stripped.1, affordable, valueEq, memory, stripped.2⟩

end InitECandidate.Solver.GasBudget.StateCharge

#print axioms InitECandidate.Solver.GasBudget.StateCharge.normal_affordable
#print axioms InitECandidate.Solver.GasBudget.StateCharge.body_bound
