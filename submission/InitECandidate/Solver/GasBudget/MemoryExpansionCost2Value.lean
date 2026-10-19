import InitECandidate.Solver.GasBudget.MemoryExpansionCost2First

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

/-- Actual normal cost2 execution restores the temporary length mutation.
This is deliberately a normal-outcome contract: timeout during the second
call can still expose the temporary length word. -/
theorem normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame current : BitVec 64)
    (s1 n1 s2 n2 : U256Value.Words) (view : MemoryExpansionCost.View source frame current)
    (start1 : source.locals.lookup (ofString "s1") = some (U256Value.tuple s1))
    (size1 : source.locals.lookup (ofString "n1") = some (U256Value.tuple n1))
    (start2 : source.locals.lookup (ofString "s2") = some (U256Value.tuple s2))
    (size2 : source.locals.lookup (ofString "n2") = some (U256Value.tuple n2))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current) ∧
      ∃ paid : Nat, paid ≤ 42 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        post.memory = source.memory ∧ Input.LocalEffects.erase post = Input.LocalEffects.erase source := by
  rw [body_shape] at run
  have args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) [localVar "s1", localVar "n1"] = some [U256Value.tuple s1, U256Value.tuple n1] := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, start1, size1]
  obtain ⟨firstPaid, ready, inner, positive, firstBound, firstFits, readyEq, fields, tailRun, scopeEq⟩ :=
    MemoryExpansionCost.normal_prefix source post frame current s1 n1 view "a" [localVar "s1", localVar "n1"] afterA returned args run
  have readyView := view.after_erase fields
  have readyA := Input.KnownUnaryPrefix.lookup_same readyEq
  have readyStart := (Input.KnownUnaryPrefix.lookup_other readyEq "s2" (by decide)).trans start2
  have readySize := (Input.KnownUnaryPrefix.lookup_other readyEq "n2" (by decide)).trans size2
  obtain ⟨value, restPaid, restBound, restFits, restClock, restMemory, restFields⟩ :=
    first_normal ready inner frame current (MemoryExpansionCost.resultPair s1 n1 current) s2 n2 readyView readyA readyStart readySize returned tailRun
  have returnedEq : returned = MemoryExpansionCost.pairValue (resultPair s1 n1 s2 n2 current) := by simpa only [resultPair] using value
  have readyClock : ready.clock = source.clock - firstPaid := by rw [readyEq]; rfl
  have readyMemory := Input.LocalEffects.memory_of_erase source ready fields
  refine ⟨returnedEq, firstPaid + restPaid, by omega, ?_, ?_, ?_, ?_⟩
  · rw [readyClock] at restFits
    omega
  · rw [scopeEq]
    change inner.clock = _
    rw [restClock, readyClock]
    omega
  · rw [scopeEq]
    exact restMemory.trans readyMemory
  · have scopes : Input.LocalEffects.erase post = Input.LocalEffects.erase inner := by rw [scopeEq]; rfl
    exact scopes.trans (restFields.trans fields)

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.normal
