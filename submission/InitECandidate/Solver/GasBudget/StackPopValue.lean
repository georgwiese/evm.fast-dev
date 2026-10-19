import InitECandidate.Solver.GasBudget.StackPopsValues

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

theorem value_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (name : String) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame))) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) shape (ofString "stack_pop") [] continuation) = (some (.returned value), post)) :
    ∃ (words : U256Value.Words) (ready inner : PanSemStateFiniteExact 64 Guest.HostMemory),
      PrefixEffect source ready frame 1 ∧ ready.locals.lookup (ofString name) = some (U256Value.tuple words) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (wordAt ready.memory (frame + 16#64)).toNat + 1 = (wordAt source.memory (frame + 16#64)).toNat := by
  obtain ⟨fits, sp, returned, inner, mapped, spCell, nonzero, typed, run, postEq, budget, used⟩ :=
    call_normal source post frame name continuation code ev value normal
  have shape : shapeOfHOLExact returned = U256Value.tupleShape := (shapeEqHOL_eq_true _ _).mp typed
  obtain ⟨words, returnedEq⟩ := U256Value.of_shape returned shape
  subst returned
  let ready := resumed source frame sp name (U256Value.tuple words)
  have positive : (1#64 : BitVec 64) ≤ sp := by
    apply BitVec.le_def.mpr
    by_contra small
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    change sp.toNat = 0
    change ¬ 1 ≤ sp.toNat at small
    omega
  have readyCell : ready.memory (frame + 16#64) = .word (sp - 1#64) := by simp [ready, resumed, setVarHOLFinite, StoreWord.put]
  refine ⟨words, ready, inner, PrefixEffect.resumed source frame sp name _ fits, ?_, run, ?_, ?_, ?_⟩
  · simp [ready, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
  · rw [postEq]; rfl
  · rw [postEq]; rfl
  · simp only [wordAt, readyCell, spCell, MemoryBytes.wordBits, BitVec.toNat_sub_of_le positive]
    change sp.toNat - 1 + 1 = sp.toNat
    have bound : 1 ≤ sp.toNat := BitVec.le_def.mp positive
    omega

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.value_normal
