import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Program

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

set_option maxHeartbeats 1000000 in
theorem final_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (a b : BitVec 64 × BitVec 64)
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))) (mapped : source.memaddrs (frame + 32#64))
    (savedLocal : source.locals.lookup (ofString "saved") = some (.val (.word current)))
    (aLocal : source.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a))
    (bLocal : source.locals.lookup (ofString "b") = some (MemoryExpansionCost.pairValue b)) :
    evaluateHOLFiniteState source afterB = (some (.returned (MemoryExpansionCost.pairValue (merge a b))),
      emptyLocalsHOLFinite {source with memory := StoreWord.put source.memory (frame + 32#64) current}) := by
  have storeRun := StoreWord.execute source (frameAddress 32#64) (localVar "saved") (frame + 32#64) current
    (address_read source frame 32#64 ev) (by simp [eval, evalHOLExact, toExact, localVar, savedLocal]) mapped
  let stored := {source with memory := StoreWord.put source.memory (frame + 32#64) current}
  have storedA : stored.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a) := aLocal
  have storedB : stored.locals.lookup (ofString "b") = some (MemoryExpansionCost.pairValue b) := bLocal
  rw [afterB, StateSteps.next_sequence source stored _ _ storeRun (Nat.le_refl _)]
  by_cases maximum : b.1 = 18446744073709551615#64
  · have guarded : evaluateHOLFiniteState stored (maxGuard "b") = (some (.returned (MemoryExpansionCost.pairValue b)), emptyLocalsHOLFinite stored) := by
      simp [maxGuard, part, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact,
        toExact, localVar, storedB, MemoryExpansionCost.pairValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        maximum, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [StateSteps.stopped_sequence stored _ (maxGuard "b") finish _ guarded (Nat.le_refl _), merge, if_pos maximum]
  · have guarded : evaluateHOLFiniteState stored (maxGuard "b") = (none, stored) := by
      simp [maxGuard, part, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        storedB, MemoryExpansionCost.pairValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, maximum]
    rw [StateSteps.next_sequence stored stored (maxGuard "b") finish guarded (Nat.le_refl _), merge, if_neg maximum]
    simp [finish, part, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact, toExact, localVar, storedA, storedB,
      MemoryExpansionCost.pairValue, valueIsWord, valueWord, wordOpHOL, wordOp, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rfl

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.final_execute
