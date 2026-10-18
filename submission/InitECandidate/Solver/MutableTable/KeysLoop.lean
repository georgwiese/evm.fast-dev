import InitECandidate.Solver.MutableTable.KeysStep

namespace InitECandidate.Solver.MutableTable.Keys
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Complete original signed key-enumeration loop. Each row derives the
dense-order read and actual padded-stride copy, while retaining the old
table and every word outside the reserved output buffer. -/
theorem loop_execute (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan) (start : Nat) (slots : List Nat)
    (outValid : MemoryRegion.Valid (outputRegion kind start slots.length))
    (earlier : ∀ pool, plan.base pool + size kind plan pool ≤ start) (remaining : Nat)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : source.memaddrs = InitE.ordinaryDomain)
    (cursor : Nat) (count : cursor + remaining = slots.length) (occupied : MemoryModel.Occupied source kind plan slots)
    (locals : Locals source kind plan start slots.length cursor)
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (enough : (rowPrice kind + 1) * remaining ≤ source.clock) :
    ∃ paid memory target, paid ≤ (rowPrice kind + 1) * remaining ∧
      evaluateHOLFiniteState source loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      Locals target kind plan start slots.length slots.length ∧
      MemoryModel.PoolFrame source.memory memory kind plan ∧ MemoryModel.Occupied target kind plan slots ∧
      (∀ query : BitVec 64, query.toNat < start ∨ start + stride kind * slots.length + 8 ≤ query.toNat → memory query = source.memory query) := by
  induction remaining generalizing source cursor with
  | zero =>
    have finished : cursor = slots.length := by omega
    have test := condition_read source kind plan valid start slots.length cursor (MemoryModel.Occupied.length_le source kind plan slots occupied) (by omega) locals
    rw [if_neg (show ¬ cursor < slots.length from by omega)] at test
    refine ⟨0, source.memory, source, by simp, ?_, by simp only [Nat.sub_zero], by simpa only [finished] using locals, MemoryModel.PoolFrame.refl _ _ _, occupied, ?_⟩
    · rw [loop, evaluateHOLFiniteState_while_total, test]; simp
    · intro query outside; rfl
  | succ remaining ih =>
    have active : cursor < slots.length := by omega
    have funded : (rowPrice kind + 1) * remaining + (rowPrice kind + 1) ≤ source.clock := by
      simpa only [Nat.mul_add, Nat.mul_one] using enough
    have positive : source.clock ≠ 0 := by omega
    let entry := decClockHOLFinite source
    have entryLocals := Locals.of_locals source entry kind plan start slots.length cursor locals rfl
    have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
    obtain ⟨paid, memory, bounded, bodyRun, poolFrame, nextModel, outsideFrame⟩ := step_execute entry kind plan valid domain start slots entryModel outValid earlier cursor active entryLocals copyCode
      (by change rowPrice kind ≤ source.clock - 1; omega)
    let next := nextState entry memory paid cursor
    have nextLocals := Locals.next entry kind plan start slots.length cursor entryLocals memory paid
    obtain ⟨restPaid, finalMemory, target, restBound, restRun, restFrame, finalLocals, restPoolFrame, finalModel, restOutside⟩ :=
      ih next domain (cursor + 1) (by omega) nextModel nextLocals copyCode
        (by change (rowPrice kind + 1) * remaining ≤ source.clock - 1 - paid; omega)
    have totalBound : 1 + paid + restPaid ≤ (rowPrice kind + 1) * (remaining + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    have frameEq : emptyLocalsHOLFinite {next with memory := finalMemory, clock := next.clock - restPaid} =
        emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - (1 + paid + restPaid)} := by
      change emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - 1 - paid - restPaid} = _
      have subtract : source.clock - 1 - paid - restPaid = source.clock - (1 + paid + restPaid) := by omega
      rw [subtract]
    refine ⟨1 + paid + restPaid, finalMemory, target, totalBound, ?_, restFrame.trans frameEq, finalLocals,
      MemoryModel.PoolFrame.trans _ _ _ kind plan poolFrame restPoolFrame, finalModel, ?_⟩
    · have test := condition_read source kind plan valid start slots.length cursor (MemoryModel.Occupied.length_le source kind plan slots occupied) (by omega) locals
      rw [if_pos active] at test
      rw [loop, evaluateHOLFiniteState_while_total, test]
      simp only [show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte, if_neg positive]
      rw [bodyRun, StateSteps.fixed_clock entry next none (by change source.clock - 1 - paid ≤ source.clock - 1; omega)]
      exact restRun
    · intro query outside
      exact (restOutside query outside).trans (outsideFrame query outside)

end InitECandidate.Solver.MutableTable.Keys

#print axioms InitECandidate.Solver.MutableTable.Keys.loop_execute
