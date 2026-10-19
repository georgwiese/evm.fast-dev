import InitECandidate.Solver.GasBudget.MemoryExpansionCostEnd
import InitECandidate.Solver.GasBudget.SaturatingAddPrefix

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch
open Input.RlpWrite

theorem saturated_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (start size : U256Value.Words) (view : View source frame current)
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source afterZero = (some (.returned returned), post)) :
    returned = pairValue (endPair current (SaturatingAdd.resultWord (SatWord.resultWord start) (SatWord.resultWord size))) := by
  have readStart : eval source (localVar "start") = some (U256Value.tuple start) := by simp [eval, localVar, evalHOLExact, toExact, startLocal]
  obtain ⟨paidS, first, firstPost, nonzeroS, boundS, fitsS, firstEq, firstFields, firstRun, firstPostEq⟩ :=
    MemoryCostCalls.normal .sat source post "s" (localVar "start") afterS start returned view.installed readStart normal
  have firstS : first.locals.lookup (ofString "s") = some (.val (.word (SatWord.resultWord start))) := Input.KnownUnaryPrefix.lookup_same firstEq
  have firstSize := (Input.KnownUnaryPrefix.lookup_other firstEq "size" (by decide)).trans sizeLocal
  have firstView := view.after_erase firstFields
  have readSize : eval first (localVar "size") = some (U256Value.tuple size) := by simp [eval, localVar, evalHOLExact, toExact, firstSize]
  obtain ⟨paidN, second, secondPost, nonzeroN, boundN, fitsN, secondEq, secondFields, secondRun, secondPostEq⟩ :=
    MemoryCostCalls.normal .sat first firstPost "n" (localVar "size") afterN size returned firstView.installed readSize firstRun
  have secondS := (Input.KnownUnaryPrefix.lookup_other secondEq "s" (by decide)).trans firstS
  have secondN : second.locals.lookup (ofString "n") = some (.val (.word (SatWord.resultWord size))) := Input.KnownUnaryPrefix.lookup_same secondEq
  have secondView := firstView.after_erase secondFields
  have addCode := OriginalCodeEnvironment.arithmetic second.code secondView.installed .add_sat
  rw [ChargeWithMemory.add_signature] at addCode
  obtain ⟨a, b, inner, funded, arguments, lower, tailRun, scopeEq⟩ :=
    SaturatingAdd.normal_prefix second secondPost "endp" [localVar "s", localVar "n"] afterEnd addCode returned secondRun
  have expectedArgs : evalListHOLFinite second (h := fun address => Classical.propDecidable (second.memaddrs address))
      [localVar "s", localVar "n"] = some [.val (.word (SatWord.resultWord start)), .val (.word (SatWord.resultWord size))] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, secondS, secondN]
  have argumentsEq := Option.some.inj (arguments.symm.trans expectedArgs)
  have aEq : a = SatWord.resultWord start := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj argumentsEq).1)
  have bEq : b = SatWord.resultWord size := HolWordLab.word.inj (ValueHOL.val.inj (List.cons.inj (List.cons.inj argumentsEq).2).1)
  let ready := WitnessRadix.QueryBranch.bind {second with clock := second.clock - 1} "endp" (SaturatingAdd.resultWord a b)
  have readyView : View ready frame current := secondView.after_erase rfl
  have endLocal : ready.locals.lookup (ofString "endp") = some (.val (.word (SaturatingAdd.resultWord a b))) := bind_lookup_same _ _ _
  have result := end_normal ready inner frame current (SaturatingAdd.resultWord a b) readyView endLocal returned tailRun
  simpa only [aEq, bEq] using result

end InitECandidate.Solver.GasBudget.MemoryExpansionCost

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost.saturated_normal
