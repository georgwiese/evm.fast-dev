import InitECandidate.Solver.GasBudget.ChargeWithMemoryProgram
import InitECandidate.Solver.GasBudget.PrefixEnvironment
import InitECandidate.Solver.Input.PricedReadOnlyPrefix

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem setup_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (baseCell : source.locals.lookup (ofString "base") = some (.val (.word base)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned value), post)) :
    ∃ paid amount ready inner, paid ≤ 22 ∧ base ≤ amount ∧ StackPop.PrefixEffect source ready frame paid ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] amount suffix) = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at normal
  obtain ⟨paid, x, firstPost, positive, bound, fits, restRun, postEq⟩ :=
    Input.PricedReadOnlyPrefix.normal source post "x" pair (ofString "extend_memory_cost1")
      [localVar "start", localVar "size"] afterCost MemoryCostEffects.Kind.extend_memory_cost1.signature.1
      MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2 20
      (MemoryCostEffects.entry source.code installed .extend_memory_cost1)
      (MemoryCostEffects.pure_extend_memory_cost1 source.code installed)
      (MemoryCostEffects.price_extend_memory_cost1 source.code installed) value normal
  let first := setVarHOLFinite (ofString "x") x {source with clock := source.clock - paid}
  have before : StackPop.PrefixEffect source first frame paid := StackPop.PrefixEffect.unchanged source first frame paid fits rfl rfl
  have firstBase : first.locals.lookup (ofString "base") = some (.val (.word base)) := by
    simpa [first, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "x" ≠ ofString "base" from by decide] using baseCell
  have addCode := OriginalCodeEnvironment.arithmetic first.code installed .add_sat
  rw [add_signature] at addCode
  obtain ⟨a, b, inner, funded, arguments, lower, chargeRun, scopeEq⟩ :=
    SaturatingAdd.normal_prefix first firstPost "total" [localVar "base", .rfield 0 (localVar "x")] afterTotal addCode value restRun
  have readBase : eval first (localVar "base") = some (.val (.word base)) := by
    simp [eval, localVar, evalHOLExact, toExact, firstBase]
  have actualBase : a = base := Input.ArgumentValues.first_of_pair first (localVar "base") (.rfield 0 (localVar "x")) base a b readBase arguments
  let ready := bind {first with clock := first.clock - 1} "total" (SaturatingAdd.resultWord a b)
  have afterTotal : StackPop.PrefixEffect first ready frame 1 := StackPop.PrefixEffect.unchanged first ready frame 1 funded rfl rfl
  have totalCell : ready.locals.lookup (ofString "total") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
  rw [charge_choice ready _ totalCell] at chargeRun
  refine ⟨paid + 1, SaturatingAdd.resultWord a b, ready, inner, by omega, ?_, before.trans afterTotal, chargeRun, ?_⟩
  · rw [← actualBase]
    exact lower
  · rw [postEq, scopeEq]
    rfl

theorem setup_exception (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame base : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (baseCell : source.locals.lookup (ofString "base") = some (.val (.word base)))
    (identifier : MlS) (payload : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.exception identifier payload), post)) :
    ∃ paid amount ready inner, paid ≤ 22 ∧ base ≤ amount ∧ StackPop.PrefixEffect source ready frame paid ∧
      evaluateHOLFiniteState ready (OpcodeChargePrefix.program [] amount suffix) = (some (.exception identifier payload), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner := by
  rw [body_shape] at run
  obtain ⟨paid, x, firstPost, positive, bound, fits, restRun, postEq⟩ :=
    Input.PricedReadOnlyPrefix.exception source post "x" pair (ofString "extend_memory_cost1")
      [localVar "start", localVar "size"] afterCost MemoryCostEffects.Kind.extend_memory_cost1.signature.1
      MemoryCostEffects.Kind.extend_memory_cost1.body MemoryCostEffects.Kind.extend_memory_cost1.signature.2.2 20
      (MemoryCostEffects.entry source.code installed .extend_memory_cost1)
      (MemoryCostEffects.pure_extend_memory_cost1 source.code installed)
      (MemoryCostEffects.price_extend_memory_cost1 source.code installed)
      (MemoryCostEffects.safe_extend_memory_cost1 source.code installed) identifier payload run
  let first := setVarHOLFinite (ofString "x") x {source with clock := source.clock - paid}
  have before : StackPop.PrefixEffect source first frame paid := StackPop.PrefixEffect.unchanged source first frame paid fits rfl rfl
  have firstBase : first.locals.lookup (ofString "base") = some (.val (.word base)) := by
    simpa [first, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE,
      show ofString "x" ≠ ofString "base" from by decide] using baseCell
  have addCode := OriginalCodeEnvironment.arithmetic first.code installed .add_sat
  rw [add_signature] at addCode
  obtain ⟨a, b, inner, funded, arguments, lower, chargeRun, scopeEq⟩ :=
    SaturatingAdd.exception_prefix first firstPost "total" [localVar "base", .rfield 0 (localVar "x")] afterTotal addCode identifier payload restRun
  have readBase : eval first (localVar "base") = some (.val (.word base)) := by
    simp [eval, localVar, evalHOLExact, toExact, firstBase]
  have actualBase : a = base := Input.ArgumentValues.first_of_pair first (localVar "base") (.rfield 0 (localVar "x")) base a b readBase arguments
  let ready := bind {first with clock := first.clock - 1} "total" (SaturatingAdd.resultWord a b)
  have afterTotal : StackPop.PrefixEffect first ready frame 1 := StackPop.PrefixEffect.unchanged first ready frame 1 funded rfl rfl
  have totalCell : ready.locals.lookup (ofString "total") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
  rw [charge_choice ready _ totalCell] at chargeRun
  refine ⟨paid + 1, SaturatingAdd.resultWord a b, ready, inner, by omega, ?_, before.trans afterTotal, chargeRun, ?_⟩
  · rw [← actualBase]
    exact lower
  · rw [postEq, scopeEq]
    rfl

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.setup_normal

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.setup_exception
