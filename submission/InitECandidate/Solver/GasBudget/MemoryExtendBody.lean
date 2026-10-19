import InitECandidate.Solver.GasBudget.MemoryExtendBodyEntry

namespace InitECandidate.Solver.GasBudget.MemoryExtend
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch WitnessRadix

def price (length capacity expand : BitVec 64) : Nat :=
  if expand = 0#64 then 0 else bodyPrice length capacity expand

theorem return_zero (source : PanSemStateFiniteExact 64 Guest.HostMemory) :
    evaluateHOLFiniteState source returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
  simp [returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
theorem body_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame base length capacity pointer scratch expand amount : BitVec 64) (used : Nat) (returned : ValueHOL 64)
    (view : View source frame base length capacity pointer scratch)
    (advance : MemoryExpansionCost.Advance length expand amount used)
    (expandLocal : source.locals.lookup (ofString "expand_by") = some (.val (.word expand)))
    (normal : evaluateHOLFiniteState source body = (some (.returned returned), post)) :
    returned = .val (.word 0#64) ∧ price length capacity expand ≤ source.clock ∧
      post.clock = source.clock - price length capacity expand ∧
      View post frame base (newLength length expand) (nextCapacity length capacity expand) (base + nextCapacity length capacity expand) scratch ∧
      Input.LocalEffects.erase post = Input.LocalEffects.erase
        (if expand = 0#64 then source else expandedState source frame base length capacity pointer expand) ∧
      (∀ query, Arenas.Outside base scratch query → query ≠ frame + 32#64 → query ≠ frame + 40#64 → post.memory query = source.memory query) := by
  by_cases zero : expand = 0#64
  · have guarded : evaluateHOLFiniteState source zeroGuard = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite source) := by
      have guard : evaluateHOLFiniteState source zeroGuard = evaluateHOLFiniteState source returnZero := by
        simp [zeroGuard, evaluateHOLFiniteState_ite, evalHOLExact, toExact, localVar, expandLocal, zero,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact guard.trans (return_zero source)
    rw [body_shape, StateSteps.stopped_sequence source _ zeroGuard afterZero _ guarded (Nat.le_refl _)] at normal
    have value : returned = .val (.word 0#64) := PanSemResultExact.returned.inj (Option.some.inj (congrArg Prod.fst normal).symm)
    have postEq : post = emptyLocalsHOLFinite source := (congrArg Prod.snd normal).symm
    have noGrow : ¬ capacity < length := by
      intro grow
      have lower := BitVec.lt_def.mp grow
      have depth := view.depth
      omega
    have nextLength : newLength length expand = length := by simp [newLength, zero]
    have nextCapacityEq : nextCapacity length capacity expand = capacity := by simp [nextCapacity, nextLength, noGrow]
    have pointerEq : pointer = base + capacity := by
      apply BitVec.eq_of_toNat_eq
      have fits : base.toNat + capacity.toNat < 2 ^ 64 := by have bound := pointer.isLt; have cursor := view.cursor; omega
      rw [BitVec.toNat_add_of_lt fits]
      exact view.cursor
    have finalView : View post frame base (newLength length expand) (nextCapacity length capacity expand) (base + nextCapacity length capacity expand) scratch := by
      rw [nextLength, nextCapacityEq, ← pointerEq]
      exact view.after_erase (by rw [postEq]; rfl)
    refine ⟨value, by simp [price, zero], ?_, finalView, ?_, ?_⟩
    · rw [postEq]; simp [price, zero, emptyLocalsHOLFinite]
    · rw [if_pos zero, postEq]; rfl
    · intro query _ _ _; rw [postEq]; rfl
  · obtain ⟨ready, inner, readyFields, readyClock, lengthLocal, capLocal, readyExpand, nlenLocal, innerRun, postFields, postClock⟩ :=
      body_entry source post frame base length capacity pointer scratch expand returned view expandLocal zero normal
    have readyView := view.after_erase readyFields
    obtain ⟨value, funded, exactPost, lengthCell, capacityCell, region, away⟩ :=
      tail_normal ready inner frame base length capacity pointer scratch expand amount used returned readyView advance lengthLocal capLocal readyExpand nlenLocal innerRun
    have innerView := tail_view ready inner frame base length capacity pointer scratch expand amount used readyView advance exactPost lengthCell capacityCell region away
    have memory : ready.memory = source.memory := Input.LocalEffects.memory_of_erase source ready readyFields
    have transported : Input.LocalEffects.erase (expandedState ready frame base length capacity pointer expand) =
        Input.LocalEffects.erase (expandedState source frame base length capacity pointer expand) := by
      have result := congrArg (fun state => Input.LocalEffects.erase (expandedState state frame base length capacity pointer expand)) readyFields
      by_cases grow : capacity < newLength length expand
      all_goals simpa only [expandedState, capacityState, grow, ↓reduceIte, growthState, Arenas.post,
        Input.LocalEffects.erase, emptyLocalsHOLFinite] using result
    refine ⟨value, ?_, ?_, innerView.after_erase postFields, ?_, ?_⟩
    · simpa only [price, if_neg zero, readyClock] using funded
    · rw [postClock, exactPost]
      change ready.clock - bodyPrice length capacity expand = _
      rw [readyClock, price, if_neg zero]
    · rw [if_neg zero]
      exact postFields.trans ((congrArg Input.LocalEffects.erase exactPost).trans transported)
    · intro query outside notLength notCapacity
      rw [Input.LocalEffects.memory_of_erase inner post postFields, away query outside notLength notCapacity, memory]

end InitECandidate.Solver.GasBudget.MemoryExtend

#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.return_zero
#print axioms InitECandidate.Solver.GasBudget.MemoryExtend.body_normal
