import InitECandidate.Solver.GasBudget.StackPopCallNormal

namespace InitECandidate.Solver.GasBudget.StackPop
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pops : List String → ProgHOL 64 → ProgHOL 64
  | [], continuation => continuation
  | name :: names, continuation => .decCall (ofString name) shape (ofString "stack_pop") [] (pops names continuation)

/-- A literal list of original stack_pop declarations reaches its actual
continuation without changing the gas cells or nonlocal metadata. Every
callee clock and successful underflow check comes from normal execution. -/
theorem pops_normal (names : List String) (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (frame : BitVec 64)
    (continuation : ProgHOL 64)
    (code : source.code.lookup (ofString "stack_pop") = some ([], body, shape))
    (ev : source.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source (pops names continuation) = (some (.returned value), post)) :
    ∃ ready inner, names.length ≤ source.clock ∧ ready.clock = source.clock - names.length ∧
      emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - names.length} ∧
      evaluateHOLFiniteState ready continuation = (some (.returned value), inner) ∧
      emptyLocalsHOLFinite post = emptyLocalsHOLFinite inner ∧
      regularBudget ready.memory frame = regularBudget source.memory frame ∧
      ready.memory (frame + 184#64) = source.memory (frame + 184#64) ∧
      (∀ address, address ≠ frame + 16#64 → ready.memory address = source.memory address) ∧
      (wordAt ready.memory (frame + 16#64)).toNat + names.length = (wordAt source.memory (frame + 16#64)).toNat := by
  induction names generalizing source post with
  | nil => exact ⟨source, post, by simp, by simp, by simp, normal, rfl, rfl, rfl, by intros; rfl, by simp⟩
  | cons name names ih =>
    obtain ⟨positive, sp, returned, firstPost, mapped, spCell, nonzero, typed, restRun, postEq, firstBudget, firstUsed⟩ :=
      call_normal source post frame name (pops names continuation) code ev value normal
    let first := resumed source frame sp name returned
    obtain ⟨ready, inner, fits, clock, frameEq, continuationRun, innerEq, budget, usedSame, outside, depth⟩ :=
      ih first firstPost code ev restRun
    have firstClock : first.clock = source.clock - 1 := rfl
    have paid : (name :: names).length ≤ source.clock := by simp only [List.length_cons]; rw [firstClock] at fits; omega
    have sub : source.clock - 1 - names.length = source.clock - (name :: names).length := by simp only [List.length_cons]; omega
    have readyFrame : emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - (name :: names).length} := by
      change emptyLocalsHOLFinite ready = emptyLocalsHOLFinite {source with memory := ready.memory, clock := source.clock - 1 - names.length} at frameEq
      simpa only [sub] using frameEq
    have positiveDepth : (1#64 : BitVec 64) ≤ sp := by
      change 1 ≤ sp.toNat
      by_contra small
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      change sp.toNat = 0
      omega
    have firstDepth : (wordAt first.memory (frame + 16#64)).toNat + 1 = (wordAt source.memory (frame + 16#64)).toNat := by
      change (wordAt (WitnessRadix.StoreWord.put source.memory (frame + 16#64) (sp - 1#64)) (frame + 16#64)).toNat + 1 = _
      simp only [wordAt, WitnessRadix.StoreWord.put, ↓reduceIte, spCell, WitnessRadix.MemoryBytes.wordBits, BitVec.toNat_sub_of_le positiveDepth]
      change sp.toNat - 1 + 1 = sp.toNat
      have positiveNat : 1 ≤ sp.toNat := positiveDepth
      omega
    refine ⟨ready, inner, paid, ?_, readyFrame, continuationRun, ?_, budget.trans firstBudget, usedSame.trans firstUsed, ?_, ?_⟩
    · rw [clock, firstClock, sub]
    · rw [postEq]
      exact innerEq
    · intro address away
      exact (outside address away).trans (show first.memory address = source.memory address from if_neg away)
    · simp only [List.length_cons]
      omega

end InitECandidate.Solver.GasBudget.StackPop

#print axioms InitECandidate.Solver.GasBudget.StackPop.pops_normal
