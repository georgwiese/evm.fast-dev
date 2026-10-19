import InitECandidate.Solver.MutableTable.GrowRuntime.StepValues

namespace InitECandidate.Solver.MutableTable.GrowRuntime
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def loopPrice (kind : KeyHash.Kind) (cursor : Nat) : Nat → Nat
  | 0 => 0
  | remaining + 1 => cursor + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 3 + loopPrice kind (cursor + 1) remaining

/-- Whole original signed rehash loop. Each iteration derives its old-row
read and new-table mutation from actual execution. The price sums increasing
occupied counts rather than multiplying every probe by the final count. -/
theorem loop_execute_values (snapshot : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start capacity : Nat) (newValid : Valid kind (relocated kind (old.base .header) start capacity))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (oldSlots : List Nat) (oldRoom : oldSlots.length ≤ old.capacity) (newRoom : oldSlots.length < capacity)
    (oldOccupied : MemoryModel.Occupied snapshot kind old oldSlots) (bits : Nat) (small : bits < 64) (power : capacity = 2 ^ bits)
    (source : PanSemStateFiniteExact 64 Guest.HostMemory) (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (cursor remaining : Nat) (count : cursor + remaining = oldSlots.length)
    (locals : LoopLocals source kind old oldSlots.length cursor)
    (slots : List Nat) (length : slots.length = cursor)
    (header : MemoryModel.Header source.memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 slots.length))
    (occupied : MemoryModel.Occupied source kind (relocated kind (old.base .header) start capacity) slots)
    (frame : OldArrays source snapshot kind old)
    (property : BitVec 64 → Prop)
    (oldValues : Get.OccupiedValuesHave snapshot (cell old .values 0) (BitVec.ofNat 64 old.capacity) oldSlots property)
    (values : Get.OccupiedValuesHave source (cell (relocated kind (old.base .header) start capacity) .values 0) (BitVec.ofNat 64 capacity) slots property)
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (enough : loopPrice kind cursor remaining ≤ source.clock) :
    ∃ paid memory target next, paid ≤ loopPrice kind cursor remaining ∧
      evaluateHOLFiniteState source Grow.loop = (none, target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with memory := memory, clock := source.clock - paid} ∧
      next.length = oldSlots.length ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start capacity) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start capacity) next ∧ OldArrays target snapshot kind old ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start capacity) ∧
      Get.OccupiedValuesHave target (cell (relocated kind (old.base .header) start capacity) .values 0) (BitVec.ofNat 64 capacity) next property := by
  induction remaining generalizing source cursor slots with
  | zero =>
    have last : cursor = oldSlots.length := by omega
    have test := condition_read source kind old oldValid oldSlots.length cursor oldRoom (by omega) locals
    rw [if_neg (show ¬ cursor < oldSlots.length from by omega)] at test
    refine ⟨0, source.memory, source, slots, Nat.le_refl _, ?_, ?_, by omega, header, occupied, frame, TableFootprint.Frame.refl _ _ _, values⟩
    · rw [Grow.loop, evaluateHOLFiniteState_while_total, test]
      simp
    · simp only [Nat.sub_zero]
  | succ remaining ih =>
    have active : cursor < oldSlots.length := by omega
    have priced : loopPrice kind cursor (remaining + 1) = cursor + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 3 + loopPrice kind (cursor + 1) remaining := rfl
    have nonzero : source.clock ≠ 0 := by rw [priced] at enough; omega
    let entry := decClockHOLFinite source
    have entryLocals : LoopLocals entry kind old oldSlots.length cursor :=
      ⟨locals.table, locals.stride, locals.keys, locals.vals, locals.order, locals.countLocal, locals.indexLocal⟩
    have entryOccupied := MemoryModel.Occupied.of_fields source entry kind _ slots occupied rfl rfl rfl
    obtain ⟨paid, memory, slot, bounded, bodyRun, nextHeader, nextOccupied, nextFrame, firstFootprint, nextValues⟩ := step_execute_values entry snapshot kind old oldValid start capacity newValid earlier domain little
      oldSlots oldRoom oldOccupied frame ⟨cursor, active⟩ entryLocals slots (by omega) header entryOccupied property oldValues values bits small power hashCode copyCode insertCode
      (by change slots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock - 1; rw [priced] at enough; omega)
    let nextState := WitnessRadix.QueryBranch.bind {entry with memory := memory, clock := entry.clock - paid} "k" (BitVec.ofNat 64 (cursor + 1))
    have nextLocals : LoopLocals nextState kind old oldSlots.length (cursor + 1) := LoopLocals.next entry kind old _ _ entryLocals memory paid
    have model := MemoryModel.Occupied.of_fields _ nextState kind _ _ nextOccupied rfl rfl rfl
    have oldFrame := OldArrays.of_memory _ nextState snapshot kind old rfl nextFrame
    have nextEnough : loopPrice kind (cursor + 1) remaining ≤ nextState.clock := by
      change loopPrice kind (cursor + 1) remaining ≤ source.clock - 1 - paid
      rw [priced] at enough
      omega
    obtain ⟨restPaid, finalMemory, target, finalSlots, restBound, actual, restFrame, finalLength, finalHeader, finalOccupied, finalFrame, restFootprint, finalValues⟩ :=
      ih nextState domain little (cursor + 1) (by omega) nextLocals (slots ++ [slot]) (by simp [length]) nextHeader model oldFrame nextValues hashCode copyCode insertCode nextEnough
    have totalBound : 1 + paid + restPaid ≤ loopPrice kind cursor (remaining + 1) := by rw [priced]; omega
    have frameEq : emptyLocalsHOLFinite {nextState with memory := finalMemory, clock := nextState.clock - restPaid} =
        emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - (1 + paid + restPaid)} := by
      change emptyLocalsHOLFinite {source with memory := finalMemory, clock := source.clock - 1 - paid - restPaid} = _
      have subtract : source.clock - 1 - paid - restPaid = source.clock - (1 + paid + restPaid) := by omega
      rw [subtract]
    refine ⟨1 + paid + restPaid, finalMemory, target, finalSlots, totalBound, ?_, restFrame.trans frameEq, finalLength, finalHeader, finalOccupied, finalFrame, TableFootprint.Frame.trans source.memory memory finalMemory kind _ firstFootprint restFootprint, finalValues⟩
    have test := condition_read source kind old oldValid oldSlots.length cursor oldRoom (by omega) locals
    rw [if_pos active] at test
    rw [Grow.loop, evaluateHOLFiniteState_while_total, test]
    simp only [show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte, if_neg nonzero]
    rw [bodyRun, StateSteps.fixed_clock entry nextState none (by change source.clock - 1 - paid ≤ source.clock - 1; omega)]
    exact actual

end InitECandidate.Solver.MutableTable.GrowRuntime

#print axioms InitECandidate.Solver.MutableTable.GrowRuntime.loop_execute_values
