import InitECandidate.Solver.GasBudget.StackPopPrefixEffect
import InitECandidate.Solver.Input.RlpWrite.U256Shape

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch Input.RlpWrite

theorem pair_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (firstName secondName : String) (distinct : ofString firstName ≠ ofString secondName)
    (continuation : ProgHOL 64) (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (pops [firstName, secondName] continuation) = (some (.returned value), post)) :
    ∃ (left right : U256Value.Words) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      PrefixEffect source ready frame 2 ∧
      ready.locals.lookup (ofString firstName) = some (U256Value.tuple left) ∧
      ready.locals.lookup (ofString secondName) = some (U256Value.tuple right) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 2 = (wordAt source.memory (frame + 16#64)).toNat := by
  obtain ⟨firstFits, sp, returned, firstPost, mapped, spCell, nonzero, typed, firstRun, firstScope, budget, used⟩ :=
    call_normal source post frame firstName (pops [secondName] continuation) code ev value normal
  have typedLeft : shapeOfHOLExact returned = U256Value.tupleShape := (shapeEqHOL_eq_true _ _).mp typed
  obtain ⟨left, returnedEq⟩ := U256Value.of_shape returned typedLeft
  subst returned
  let first := resumed source frame sp firstName (U256Value.tuple left)
  have firstEffect := PrefixEffect.resumed source frame sp firstName (U256Value.tuple left) firstFits
  have firstCode : first.code.lookup (ofString "stack_pop") = some ([], body, shape) := code
  have firstEV : first.globals.lookup (ofString "ev") = some (.val (.word frame)) := ev
  obtain ⟨secondFits, nextSP, returned, inner, nextMapped, nextCell, nextNonzero, typed, run, secondScope, nextBudget, nextUsed⟩ :=
    call_normal first firstPost frame secondName continuation firstCode firstEV value firstRun
  have typedRight : shapeOfHOLExact returned = U256Value.tupleShape := (shapeEqHOL_eq_true _ _).mp typed
  obtain ⟨right, returnedEq⟩ := U256Value.of_shape returned typedRight
  subst returned
  let ready := resumed first frame nextSP secondName (U256Value.tuple right)
  have secondEffect := PrefixEffect.resumed first frame nextSP secondName (U256Value.tuple right) secondFits
  have leftCell : first.locals.lookup (ofString firstName) = some (U256Value.tuple left) := by simp [first, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  have spPositive : (1#64 : BitVec 64) ≤ sp := by
    apply BitVec.le_def.mpr
    by_contra small
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change sp.toNat = 0
    change ¬ 1 ≤ sp.toNat at small
    omega
  have nextPositive : (1#64 : BitVec 64) ≤ nextSP := by
    apply BitVec.le_def.mpr
    by_contra small
    apply nextNonzero
    apply BitVec.eq_of_toNat_eq
    change nextSP.toNat = 0
    change ¬ 1 ≤ nextSP.toNat at small
    omega
  have firstCell : first.memory (frame + 16#64) = .word (sp - 1#64) := by simp [first, resumed, setVarHOLFinite, WitnessRadix.StoreWord.put]
  have nextNumber := congrArg BitVec.toNat (HolWordLab.word.inj (firstCell.symm.trans nextCell))
  rw [BitVec.toNat_sub_of_le spPositive] at nextNumber
  change sp.toNat - 1 = nextSP.toNat at nextNumber
  have readyCell : ready.memory (frame + 16#64) = .word (nextSP - 1#64) := by simp [ready, resumed, setVarHOLFinite, WitnessRadix.StoreWord.put]
  refine ⟨left, right, ready, inner, firstEffect.trans secondEffect, ?_, ?_, run, ?_, ?_, ?_⟩
  · simpa [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, distinct, Ne.symm distinct] using leftCell
  · simp [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [firstScope, secondScope]; rfl
  · rw [firstScope, secondScope]; rfl
  · simp only [wordAt, readyCell, spCell, WitnessRadix.MemoryBytes.wordBits, BitVec.toNat_sub_of_le nextPositive]
    change nextSP.toNat - 1 + 2 = sp.toNat
    have positiveNat : 1 ≤ sp.toNat := BitVec.le_def.mp spPositive
    have nextPositiveNat : 1 ≤ nextSP.toNat := BitVec.le_def.mp nextPositive
    omega

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pair_normal
