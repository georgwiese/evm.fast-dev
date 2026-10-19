import InitECandidate.Solver.GasBudget.ChargeWithMemoryProgram
import InitECandidate.Solver.GasBudget.MemoryExpansionCostPrefix
import InitECandidate.Solver.Input.KnownUnaryPrefix

namespace InitECandidate.Solver.GasBudget.ChargeWithMemory
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem setup_value (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current base : BitVec 64)
    (start size : U256Value.Words) (view : MemoryExpansionCost.View source frame current)
    (baseLocal : source.locals.lookup (ofString "base") = some (.val (.word base)))
    (startLocal : source.locals.lookup (ofString "start") = some (U256Value.tuple start))
    (sizeLocal : source.locals.lookup (ofString "size") = some (U256Value.tuple size))
    (returned : ValueHOL 64) (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    ∃ (paid : Nat) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      1 ≤ paid ∧ paid ≤ 22 ∧ paid ≤ source.clock ∧
      Input.LocalEffects.erase ready = Input.LocalEffects.erase source ∧ ready.clock = source.clock - paid ∧
      ready.locals.lookup (ofString "x") = some (MemoryExpansionCost.pairValue (MemoryExpansionCost.resultPair start size current)) ∧
      ready.locals.lookup (ofString "total") = some (.val (.word (SaturatingAdd.resultWord base (MemoryExpansionCost.resultPair start size current).1))) ∧
      evaluateHOLFiniteState ready afterTotal = (some (.returned returned), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock := by
  rw [body_shape] at normal
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "start", localVar "size"] = some [U256Value.tuple start, U256Value.tuple size] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, startLocal, sizeLocal]
  obtain ⟨costPaid, first, firstPost, costPositive, costBound, costFits, firstEq, firstFields, restRun, firstScope⟩ :=
    MemoryExpansionCost.normal_prefix source post frame current start size view "x" [localVar "start", localVar "size"] afterCost returned args normal
  have firstBase := (Input.KnownUnaryPrefix.lookup_other firstEq "base" (by decide)).trans baseLocal
  have firstX := Input.KnownUnaryPrefix.lookup_same firstEq
  have installed : Input.OriginalCode.Installed first.code := by rw [Input.LocalEffects.code_of_erase source first firstFields]; exact view.installed
  have addCode := OriginalCodeEnvironment.arithmetic first.code installed .add_sat
  rw [add_signature] at addCode
  obtain ⟨a, b, inner, addFits, actualArgs, lower, afterRun, secondScope⟩ :=
    SaturatingAdd.normal_prefix first firstPost "total" [localVar "base", .rfield 0 (localVar "x")] afterTotal addCode returned restRun
  have expectedArgs : evalListHOLFinite first (h := fun address => Classical.propDecidable (first.memaddrs address)) [localVar "base", .rfield 0 (localVar "x")] =
      some [.val (.word base), .val (.word (MemoryExpansionCost.resultPair start size current).1)] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, firstBase, firstX, MemoryExpansionCost.pairValue]
  have actualValues := Option.some.inj (actualArgs.symm.trans expectedArgs)
  have identified : a = base ∧ b = (MemoryExpansionCost.resultPair start size current).1 := by simpa using actualValues
  rcases identified with ⟨aEq, bEq⟩
  subst a
  subst b
  let ready := bind {first with clock := first.clock - 1} "total" (SaturatingAdd.resultWord base (MemoryExpansionCost.resultPair start size current).1)
  have firstClock : first.clock = source.clock - costPaid := by rw [firstEq]; rfl
  refine ⟨costPaid + 1, ready, inner, by omega, by omega, by rw [firstClock] at addFits; omega, ?_, ?_, ?_, bind_lookup_same _ _ _, afterRun, ?_, ?_⟩
  · exact firstFields
  · change first.clock - 1 = source.clock - (costPaid + 1)
    rw [firstClock]
    omega
  · exact (bind_lookup_other _ "total" "x" _ (by decide)).trans firstX
  · rw [firstScope, secondScope]; rfl
  · rw [firstScope, secondScope]; rfl

end InitECandidate.Solver.GasBudget.ChargeWithMemory

#print axioms InitECandidate.Solver.GasBudget.ChargeWithMemory.setup_value
