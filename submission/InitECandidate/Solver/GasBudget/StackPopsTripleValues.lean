import InitECandidate.Solver.GasBudget.StackPopsValues
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

theorem triple_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (firstName secondName thirdName : String)
    (firstSecond : ofString firstName ≠ ofString secondName)
    (thirdFirst : ofString thirdName ≠ ofString firstName) (thirdSecond : ofString thirdName ≠ ofString secondName)
    (continuation : ProgHOL 64) (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (pops [firstName, secondName, thirdName] continuation) = (some (.returned value), post)) :
    ∃ (a b c : U256Value.Words) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      PrefixEffect source ready frame 3 ∧
      ready.locals.lookup (ofString firstName) = some (U256Value.tuple a) ∧
      ready.locals.lookup (ofString secondName) = some (U256Value.tuple b) ∧
      ready.locals.lookup (ofString thirdName) = some (U256Value.tuple c) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 3 = (wordAt source.memory (frame + 16#64)).toNat := by
  obtain ⟨a, b, first, firstPost, before, aCell, bCell, firstRun, firstFields, firstClock, firstDepth⟩ :=
    pair_normal source post frame firstName secondName firstSecond (pops [thirdName] continuation) code ev value normal
  have firstCode : first.code.lookup (ofString "stack_pop") = some ([], body, shape) := by rw [before.code_eq]; exact code
  have firstEv : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := by rw [before.globals_eq]; exact ev
  obtain ⟨fits, sp, returned, inner, mapped, spCell, nonzero, typed, run, scopeEq, budget, used⟩ :=
    call_normal first firstPost frame thirdName continuation firstCode firstEv value firstRun
  have checked : shapeOfHOLExact returned = U256Value.tupleShape := (shapeEqHOL_eq_true _ _).mp typed
  obtain ⟨c, returnedEq⟩ := U256Value.of_shape returned checked
  subst returned
  let ready := resumed first frame sp thirdName (U256Value.tuple c)
  have thirdEffect := PrefixEffect.resumed first frame sp thirdName (U256Value.tuple c) fits
  have positive : (1#64 : BitVec 64) ≤ sp := by
    apply BitVec.le_def.mpr
    by_contra small
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change sp.toNat = 0
    change ¬ 1 ≤ sp.toNat at small
    omega
  have readyCell : ready.memory (frame + 16#64) = .word (sp - 1#64) := by simp [ready, resumed, setVarHOLFinite, StoreWord.put]
  have lastDepth : (wordAt ready.memory (frame + 16#64)).toNat + 1 = (wordAt first.memory (frame + 16#64)).toNat := by
    simp only [wordAt, readyCell, spCell, MemoryBytes.wordBits, BitVec.toNat_sub_of_le positive]
    change sp.toNat - 1 + 1 = sp.toNat
    have number : 1 ≤ sp.toNat := BitVec.le_def.mp positive
    omega
  refine ⟨a, b, c, ready, inner, before.trans thirdEffect, ?_, ?_, ?_, run, ?_, ?_, by omega⟩
  · simpa [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, thirdFirst, Ne.symm thirdFirst] using aCell
  · simpa [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, thirdSecond, Ne.symm thirdSecond] using bCell
  · simp [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [firstFields, scopeEq]; rfl
  · rw [firstClock, scopeEq]; rfl

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.triple_normal
