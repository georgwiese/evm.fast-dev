import InitECandidate.Solver.GasBudget.MemoryExpansionCostSaturated

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

/-- Complete unchanged extend_memory_cost1 derives its actual pair from
current scalar/quad inputs and the physical current memory-length word.
Every helper run and conditional branch comes from the real normal body. -/
theorem normal_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (start size : U256Value.Words) (view : View source frame current)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = pairValue (resultPair start size current) := by
  rw [body_shape] at normal
  have read : eval source (localVar "size") = some (U256Value.tuple size) := by simp [eval, localVar, evalHOLExact, toExact, sizeLocal]
  obtain ⟨paid, ready, inner, nonzero, bound, fits, readyEq, fields, run, postEq⟩ :=
    MemoryCostCalls.normal .zero source post "z" (localVar "size") afterZ size returned view.installed read normal
  have zLocal : ready.locals.lookup (ofString "z") = some (.val (.word (U256Zero.resultWord size))) := Input.KnownUnaryPrefix.lookup_same readyEq
  have readyStart := (Input.KnownUnaryPrefix.lookup_other readyEq "start" (by decide)).trans startLocal
  have readySize := (Input.KnownUnaryPrefix.lookup_other readyEq "size" (by decide)).trans sizeLocal
  have readyView := view.after_erase fields
  by_cases zero : U256Zero.resultWord size ≠ 0#64
  · have guarded : evaluateHOLFiniteState ready zeroGuard = (some (.returned (pairValue (0#64, 0#64))), emptyLocalsHOLFinite ready) := by
      simp [zeroGuard, returnZero, pairExpression, pairValue, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, toExact, localVar, zLocal, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterZ, WitnessRadix.StateSteps.stopped_sequence ready _ zeroGuard afterZero _ guarded (Nat.le_refl _)] at run
    rw [resultPair, if_pos zero]
    exact PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst run).symm)
  · have guarded : evaluateHOLFiniteState ready zeroGuard = (none, ready) := by
      simp [zeroGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        zLocal, zero, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [afterZ, WitnessRadix.StateSteps.next_sequence ready ready zeroGuard afterZero guarded (Nat.le_refl _)] at run
    rw [resultPair, if_neg zero]
    exact saturated_normal ready inner frame current start size readyView readyStart readySize returned run

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.normal_value
