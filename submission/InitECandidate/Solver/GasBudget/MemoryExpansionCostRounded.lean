import InitECandidate.Solver.GasBudget.MemoryExpansionCostFinal

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 1000000 in
theorem rounded_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (current endp : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (curLocal : source.locals.lookup (ofString "cur") = some (.val (.word current)))
    (endLocal : source.locals.lookup (ofString "endp") = some (.val (.word endp)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterCurrent = (some (.returned returned), post)) :
    returned = pairValue (if Ceil32.resultWord endp ≤ Ceil32.resultWord current then (0#64, 0#64)
      else finalPair (Ceil32.resultWord current) (Ceil32.resultWord endp)) := by
  have readBefore : eval source (localVar "cur") = some (.val (.word current)) := by simp [eval, localVar, evalHOLExact, toExact, curLocal]
  obtain ⟨paidBefore, first, firstPost, nonzeroBefore, boundBefore, fitsBefore, firstEq, firstFields, firstRun, firstPostEq⟩ :=
    MemoryCostCalls.normal .ceil source post "before" (localVar "cur") afterBefore current returned installed readBefore normal
  have firstBefore : first.locals.lookup (ofString "before") = some (.val (.word (Ceil32.resultWord current))) := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstEnd := (Input.KnownUnaryPrefix.lookup_other firstEq "endp" (by decide)).trans endLocal
  have firstInstalled := MemoryCostCalls.installed_after firstFields installed
  have readAfter : eval first (localVar "endp") = some (.val (.word endp)) := by simp [eval, localVar, evalHOLExact, toExact, firstEnd]
  obtain ⟨paidAfter, second, secondPost, nonzeroAfter, boundAfter, fitsAfter, secondEq, secondFields, secondRun, secondPostEq⟩ :=
    MemoryCostCalls.normal .ceil first firstPost "after" (localVar "endp") afterAfter endp returned firstInstalled readAfter firstRun
  have secondBefore := (Input.KnownUnaryPrefix.lookup_other secondEq "before" (by decide)).trans firstBefore
  have secondAfter : second.locals.lookup (ofString "after") = some (.val (.word (Ceil32.resultWord endp))) := Input.KnownUnaryPrefix.lookup_same secondEq
  have secondInstalled := MemoryCostCalls.installed_after secondFields firstInstalled
  by_cases noGrowth : Ceil32.resultWord endp ≤ Ceil32.resultWord current
  · have guarded : evaluateHOLFiniteState second growthGuard = (some (.returned (pairValue (0#64, 0#64))), emptyLocalsHOLFinite second) := by
      simp [growthGuard, returnZero, pairExpression, pairValue, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, toExact, localVar, secondBefore, secondAfter, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        noGrowth, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterAfter, WitnessRadix.StateSteps.stopped_sequence second _ growthGuard afterGrowth _ guarded (Nat.le_refl _)] at secondRun
    rw [if_pos noGrowth]
    exact PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst secondRun).symm)
  · have guarded : evaluateHOLFiniteState second growthGuard = (none, second) := by
      simp [growthGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        secondBefore, secondAfter, noGrowth, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [afterAfter, WitnessRadix.StateSteps.next_sequence second second growthGuard afterGrowth guarded (Nat.le_refl _)] at secondRun
    rw [if_neg noGrowth]
    exact final_normal second secondPost (Ceil32.resultWord current) (Ceil32.resultWord endp) secondInstalled secondBefore secondAfter returned secondRun

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.rounded_normal
