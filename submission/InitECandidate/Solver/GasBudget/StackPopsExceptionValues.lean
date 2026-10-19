import InitECandidate.Solver.GasBudget.StackPopsValues
import InitECandidate.Solver.GasBudget.StackPopCallException

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

theorem pair_exception_values (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (firstName secondName : String) (distinct : ofString firstName ≠ ofString secondName)
    (continuation : ProgHOL 64) (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (mapped : source.memaddrs (frame + 16#64)) (cell : source.memory (frame + 16#64) = .word sp)
    (exceptionShape : source.eshapes.lookup (ofString "EvmErr") = some .one)
    (identifier : MlS) (payload : ValueHOL 64) (other : payload ≠ .val (.word 2#64))
    (run : evaluateHOLFiniteState source (pops [firstName, secondName] continuation) = (some (.exception identifier payload), post)) :
    ∃ (left right : U256Value.Words) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      PrefixEffect source ready frame 2 ∧
      ready.locals.lookup (ofString firstName) = some (U256Value.tuple left) ∧
      ready.locals.lookup (ofString secondName) = some (U256Value.tuple right) ∧
      evaluateHOLFiniteState ready continuation = (some (.exception identifier payload), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 2 = sp.toNat := by
  obtain ⟨firstFits, failed | continued⟩ := call_exception source post frame sp firstName (pops [secondName] continuation)
    code ev mapped cell exceptionShape identifier payload run
  · obtain ⟨zero, actualId, actualPayload, fields, clock⟩ := failed
    exact (other actualPayload).elim
  · obtain ⟨nonzero, returned, firstPost, typed, firstRun, firstScope, budget, used⟩ := continued
    obtain ⟨left, returnedEq⟩ := U256Value.of_shape returned ((shapeEqHOL_eq_true _ _).mp typed)
    subst returned
    let first := resumed source frame sp firstName (U256Value.tuple left)
    have firstEffect := PrefixEffect.resumed source frame sp firstName (U256Value.tuple left) firstFits
    have firstCell : first.memory (frame + 16#64) = .word (sp - 1#64) := by simp [first, resumed, setVarHOLFinite, StoreWord.put]
    obtain ⟨secondFits, failed | continued⟩ := call_exception first firstPost frame (sp - 1#64) secondName continuation
      code ev mapped firstCell exceptionShape identifier payload firstRun
    · obtain ⟨zero, actualId, actualPayload, fields, clock⟩ := failed
      exact (other actualPayload).elim
    · obtain ⟨nextNonzero, returned, inner, typed, tailRun, secondScope, nextBudget, nextUsed⟩ := continued
      obtain ⟨right, returnedEq⟩ := U256Value.of_shape returned ((shapeEqHOL_eq_true _ _).mp typed)
      subst returned
      let ready := resumed first frame (sp - 1#64) secondName (U256Value.tuple right)
      have secondEffect := PrefixEffect.resumed first frame (sp - 1#64) secondName (U256Value.tuple right) secondFits
      have leftCell : first.locals.lookup (ofString firstName) = some (U256Value.tuple left) := by simp [first, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      have positive : (1#64 : BitVec 64) ≤ sp := by
        apply BitVec.le_def.mpr
        by_contra small
        apply nonzero
        apply BitVec.eq_of_toNat_eq
        change sp.toNat = 0
        change ¬ 1 ≤ sp.toNat at small
        omega
      have nextPositive : (1#64 : BitVec 64) ≤ sp - 1#64 := by
        apply BitVec.le_def.mpr
        by_contra small
        apply nextNonzero
        apply BitVec.eq_of_toNat_eq
        change (sp - 1#64).toNat = 0
        change ¬ 1 ≤ (sp - 1#64).toNat at small
        omega
      have readyCell : ready.memory (frame + 16#64) = .word (sp - 1#64 - 1#64) := by simp [ready, resumed, setVarHOLFinite, StoreWord.put]
      refine ⟨left, right, ready, inner, firstEffect.trans secondEffect, ?_, ?_, tailRun, ?_, ?_, ?_⟩
      · simpa [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, distinct, Ne.symm distinct] using leftCell
      · simp [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
      · rw [firstScope, secondScope]; rfl
      · rw [firstScope, secondScope]; rfl
      · simp only [wordAt, readyCell, MemoryBytes.wordBits, BitVec.toNat_sub_of_le nextPositive, BitVec.toNat_sub_of_le positive]
        change sp.toNat - 1 - 1 + 2 = sp.toNat
        have firstNumber : 1 ≤ sp.toNat := BitVec.le_def.mp positive
        have secondNumber : 1 ≤ (sp - 1#64).toNat := BitVec.le_def.mp nextPositive
        rw [BitVec.toNat_sub_of_le positive] at secondNumber
        change 1 ≤ sp.toNat - 1 at secondNumber
        omega

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pair_exception_values
