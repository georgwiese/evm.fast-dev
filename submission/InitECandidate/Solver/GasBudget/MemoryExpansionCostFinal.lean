import InitECandidate.Solver.GasBudget.MemoryExpansionCostProgram
import InitECandidate.Solver.Input.ReturnNormal

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem final_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (before after : BitVec 64)
    (installed : Input.OriginalCode.Installed source.code)
    (beforeLocal : source.locals.lookup (ofString "before") = some (.val (.word before)))
    (afterLocal : source.locals.lookup (ofString "after") = some (.val (.word after)))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterGrowth = (some (.returned returned), post)) :
    returned = pairValue (finalPair before after) := by
  have readA : eval source (localVar "after") = some (.val (.word after)) := by simp [eval, localVar, evalHOLExact, toExact, afterLocal]
  obtain ⟨paidA, first, firstPost, nonzeroA, boundA, fitsA, firstEq, firstFields, firstRun, firstPostEq⟩ :=
    MemoryCostCalls.normal .cost source post "ca" (localVar "after") afterCA after returned installed readA normal
  have firstBefore := (Input.KnownUnaryPrefix.lookup_other firstEq "before" (by decide)).trans beforeLocal
  have firstAfter := (Input.KnownUnaryPrefix.lookup_other firstEq "after" (by decide)).trans afterLocal
  have firstCA : first.locals.lookup (ofString "ca") = some (.val (.word (MemoryGasCost.resultWord after))) :=
    Input.KnownUnaryPrefix.lookup_same firstEq
  have firstInstalled := MemoryCostCalls.installed_after firstFields installed
  have readB : eval first (localVar "before") = some (.val (.word before)) := by simp [eval, localVar, evalHOLExact, toExact, firstBefore]
  obtain ⟨paidB, second, secondPost, nonzeroB, boundB, fitsB, secondEq, secondFields, secondRun, secondPostEq⟩ :=
    MemoryCostCalls.normal .cost first firstPost "cb" (localVar "before") afterCB before returned firstInstalled readB firstRun
  have secondBefore := (Input.KnownUnaryPrefix.lookup_other secondEq "before" (by decide)).trans firstBefore
  have secondAfter := (Input.KnownUnaryPrefix.lookup_other secondEq "after" (by decide)).trans firstAfter
  have secondCA := (Input.KnownUnaryPrefix.lookup_other secondEq "ca" (by decide)).trans firstCA
  have secondCB : second.locals.lookup (ofString "cb") = some (.val (.word (MemoryGasCost.resultWord before))) :=
    Input.KnownUnaryPrefix.lookup_same secondEq
  change returned = pairValue (if MemoryGasCost.resultWord after = 18446744073709551615#64 then (18446744073709551615#64, 0#64)
    else (MemoryGasCost.resultWord after - MemoryGasCost.resultWord before, after - before))
  by_cases maximum : MemoryGasCost.resultWord after = 18446744073709551615#64
  · have guarded : evaluateHOLFiniteState second (maxGuard "ca") =
        (some (.returned (pairValue (18446744073709551615#64, 0#64))), emptyLocalsHOLFinite second) := by
      simp [maxGuard, returnMax, pairExpression, pairValue, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return,
        evalHOLExact, evalListHOLExact, toExact, localVar, secondCA, maximum, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterCB, WitnessRadix.StateSteps.stopped_sequence second _ (maxGuard "ca") finish _ guarded (Nat.le_refl _)] at secondRun
    rw [if_pos maximum]
    exact PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst secondRun).symm)
  · have guarded : evaluateHOLFiniteState second (maxGuard "ca") = (none, second) := by
      simp [maxGuard, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        secondCA, maximum, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [afterCB, WitnessRadix.StateSteps.next_sequence second second (maxGuard "ca") finish guarded (Nat.le_refl _)] at secondRun
    obtain ⟨read, finalEq⟩ := Input.return_normal second secondPost
      (.rstruct [.op .sub [localVar "ca", localVar "cb"], .op .sub [localVar "after", localVar "before"]]) returned secondRun
    have evaluated : eval second (.rstruct [.op .sub [localVar "ca", localVar "cb"], .op .sub [localVar "after", localVar "before"]]) =
        some (pairValue (MemoryGasCost.resultWord after - MemoryGasCost.resultWord before, after - before)) := by
      simp [eval, pairValue, evalHOLExact, evalListHOLExact, toExact, localVar, secondCA, secondCB, secondBefore, secondAfter,
        valueIsWord, valueWord, wordOpHOL, wordOp]
    rw [if_neg maximum]
    exact Option.some.inj (read.symm.trans evaluated)

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.final_normal
