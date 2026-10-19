import InitECandidate.Solver.GasBudget.MemoryExpansionCost2Saved

namespace InitECandidate.Solver.GasBudget.MemoryExpansionCost2
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix Input.RlpWrite

set_option maxHeartbeats 1000000 in
theorem first_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame current : BitVec 64) (a : BitVec 64 × BitVec 64) (s2 n2 : U256Value.Words)
    (view : MemoryExpansionCost.View source frame current)
    (aLocal : source.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a))
    (startLocal : source.locals.lookup (ofString "s2") = some (U256Value.tuple s2))
    (sizeLocal : source.locals.lookup (ofString "n2") = some (U256Value.tuple n2))
    (returned : ValueHOL 64) (run : evaluateHOLFiniteState source afterA = (some (.returned returned), post)) :
    returned = MemoryExpansionCost.pairValue (if a.1 = 18446744073709551615#64 then a else merge a (MemoryExpansionCost.resultPair s2 n2 (current + a.2))) ∧
      ∃ paid : Nat, paid ≤ 21 ∧ paid ≤ source.clock ∧ post.clock = source.clock - paid ∧
        post.memory = source.memory ∧ Input.LocalEffects.erase post = Input.LocalEffects.erase source := by
  by_cases maximum : a.1 = 18446744073709551615#64
  · have guarded : evaluateHOLFiniteState source (maxGuard "a") = (some (.returned (MemoryExpansionCost.pairValue a)), emptyLocalsHOLFinite source) := by
      simp [maxGuard, part, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_return, evalHOLExact, evalListHOLExact,
        toExact, localVar, aLocal, MemoryExpansionCost.pairValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        maximum, shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [afterA, StateSteps.stopped_sequence source _ (maxGuard "a") _ _ guarded (Nat.le_refl _)] at run
    have value : returned = MemoryExpansionCost.pairValue a := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst run).symm)
    have postEq : post = emptyLocalsHOLFinite source := (congrArg Prod.snd run).symm
    rw [if_pos maximum]
    refine ⟨value, 0, by decide, by simp, ?_, ?_, ?_⟩
    · rw [postEq]; simp [emptyLocalsHOLFinite]
    · rw [postEq]; rfl
    · rw [postEq]; rfl
  · have guarded : evaluateHOLFiniteState source (maxGuard "a") = (none, source) := by
      simp [maxGuard, part, evaluateHOLFiniteState_ite, evaluateHOLFiniteState_skip, evalHOLExact, toExact, localVar,
        aLocal, MemoryExpansionCost.pairValue, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, maximum]
    rw [afterA, StateSteps.next_sequence source source (maxGuard "a") _ guarded (Nat.le_refl _)] at run
    obtain ⟨inner, actual, scopeEq⟩ := Input.declaration_return_word source post "saved" (frameLoad 32#64) current afterSaved returned
      (frame_read source frame 32#64 current view.ev view.mapped view.cell) run
    let ready := WitnessRadix.QueryBranch.bind source "saved" current
    have readyView : MemoryExpansionCost.View ready frame current := view.after_erase rfl
    have saved : ready.locals.lookup (ofString "saved") = some (.val (.word current)) := bind_lookup_same _ _ _
    have readyA : ready.locals.lookup (ofString "a") = some (MemoryExpansionCost.pairValue a) := (bind_lookup_other source "saved" "a" _ (by decide)).trans aLocal
    have readyStart : ready.locals.lookup (ofString "s2") = some (U256Value.tuple s2) := (bind_lookup_other source "saved" "s2" _ (by decide)).trans startLocal
    have readySize : ready.locals.lookup (ofString "n2") = some (U256Value.tuple n2) := (bind_lookup_other source "saved" "n2" _ (by decide)).trans sizeLocal
    obtain ⟨value, paid, bound, fits, clock, memory, fields⟩ := saved_normal ready inner frame current a s2 n2 readyView saved readyA readyStart readySize returned actual
    rw [if_neg maximum]
    refine ⟨value, paid, bound, fits, ?_, ?_, ?_⟩
    · rw [scopeEq]; exact clock
    · rw [scopeEq]; exact memory
    · have scopes : Input.LocalEffects.erase post = Input.LocalEffects.erase inner := by rw [scopeEq]; rfl
      exact scopes.trans fields

end InitECandidate.Solver.GasBudget.MemoryExpansionCost2

#print axioms InitECandidate.Solver.GasBudget.MemoryExpansionCost2.first_normal
