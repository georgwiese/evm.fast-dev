import InitECandidate.Solver.GasBudget.StackPopsValues
import InitECandidate.Solver.GasBudget.PrefixEnvironment

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

private theorem resumed_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (frame sp : BitVec 64)
    (name key : String) (value : ValueHOL 64) (different : ofString name ≠ ofString key) :
    (resumed source frame sp name value).locals.lookup (ofString key) = source.locals.lookup (ofString key) := by
  simp [resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE, different, Ne.symm different]

/-- Arbitrary real distinct-name pop sequences expose all actual typed
quads and preserve other caller locals, with exact stack/clock decrement.
No argument, callee, continuation, stack depth or funding is supplied. -/
theorem pops_typed_normal (names : List String) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (distinct : (names.map ofString).Nodup) (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (pops names continuation) = (some (.returned value), post)) :
    ∃ ready inner, PrefixEffect source ready frame names.length ∧
      (∀ name ∈ names, ∃ words : U256Value.Words, ready.locals.lookup (ofString name) = some (U256Value.tuple words)) ∧
      (∀ key : String, (∀ name ∈ names, ofString name ≠ ofString key) → ready.locals.lookup (ofString key) = source.locals.lookup (ofString key)) ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase inner ∧ post.clock = inner.clock ∧
      (wordAt ready.memory (frame + 16#64)).toNat + names.length = (wordAt source.memory (frame + 16#64)).toNat := by
  induction names generalizing source post with
  | nil => exact ⟨source, post, PrefixEffect.refl source frame, by simp, by intro key away; rfl, normal, rfl, rfl, by simp⟩
  | cons name names ih =>
    have nodup := List.nodup_cons.mp distinct
    obtain ⟨fits, sp, returned, firstPost, mapped, spCell, nonzero, typed, restRun, scope, budget, used⟩ :=
      call_normal source post frame name (pops names continuation) code ev value normal
    obtain ⟨words, resultEq⟩ := U256Value.of_shape returned ((shapeEqHOL_eq_true _ _).mp typed)
    subst returned
    let first := resumed source frame sp name (U256Value.tuple words)
    have firstEffect := PrefixEffect.resumed source frame sp name (U256Value.tuple words) fits
    obtain ⟨ready, inner, effect, cells, other, tailRun, fields, clock, depth⟩ :=
      ih first firstPost nodup.2 code ev restRun
    have headCell : ready.locals.lookup (ofString name) = some (U256Value.tuple words) := by
      rw [other name (by
        intro later member equal
        exact nodup.1 (List.mem_map.mpr ⟨later, member, equal⟩))]
      simp [first, resumed, setVarHOLFinite, HolFiniteMapExact.update, FUPDATE]
    have positive : (1#64 : BitVec 64) ≤ sp := by
      change 1 ≤ sp.toNat
      by_contra small
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      change sp.toNat = 0
      omega
    have firstDepth : (wordAt first.memory (frame + 16#64)).toNat + 1 = (wordAt source.memory (frame + 16#64)).toNat := by
      simp only [first, resumed, setVarHOLFinite, wordAt, StoreWord.put, ↓reduceIte, spCell, MemoryBytes.wordBits, BitVec.toNat_sub_of_le positive]
      change sp.toNat - 1 + 1 = sp.toNat
      have bound : 1 ≤ sp.toNat := positive
      omega
    refine ⟨ready, inner, ?_, ?_, ?_, tailRun, ?_, ?_, ?_⟩
    · simpa only [List.length_cons, Nat.add_comm] using firstEffect.trans effect
    · intro key member
      rcases List.mem_cons.mp member with rfl | member
      · exact ⟨words, headCell⟩
      · exact cells key member
    · intro key away
      exact (other key (by intro later member; exact away later (by simp [member]))).trans
        (resumed_other source frame sp name key (U256Value.tuple words) (away name (by simp)))
    · rw [scope]; exact fields
    · rw [scope]; exact clock
    · simp only [List.length_cons]
      omega

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pops_typed_normal
