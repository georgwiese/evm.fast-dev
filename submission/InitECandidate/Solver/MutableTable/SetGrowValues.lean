import InitECandidate.Solver.MutableTable.SetGrowGuard
import InitECandidate.Solver.MutableTable.GrowRuntime.CallValues

namespace InitECandidate.Solver.MutableTable.Set
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def afterGrowPrice (kind : KeyHash.Kind) (capacity count : Nat) :=
  GrowRuntime.price kind (2 * capacity) count + 1 + count + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2

/-- Actual absent-key growing setter suffix: derive the original guard,
execute growth, insert into its returned physical table, then return. Entry
allocation/query/code reachability remains explicit; neither mutation result
nor its execution is an input hypothesis. -/
theorem after_grow_values (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (old : Plan)
    (oldValid : Valid kind old) (start : Nat) (newValid : Valid kind (relocated kind (old.base .header) start (2 * old.capacity)))
    (earlier : ∀ pool, old.base pool + size kind old pool ≤ start)
    (domain : source.memaddrs = InitE.ordinaryDomain) (little : source.be = false)
    (slots : List Nat) (header : MemoryModel.Header source.memory kind old (BitVec.ofNat 64 slots.length)) (occupied : MemoryModel.Occupied source kind old slots)
    (property : BitVec 64 → Prop)
    (values : Get.OccupiedValuesHave source (cell old .values 0) (BitVec.ofNat 64 old.capacity) slots property)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell old .header 0))))
    (query value : BitVec 64) (keyLocal : source.locals.lookup (ofString "key") = some (.val (.word query)))
    (valueLocal : source.locals.lookup (ofString "value") = some (.val (.word value)))
    (queryFits : query.toNat + KeyHash.keySize kind < 2 ^ 64)
    (queryMapped : ∀ offset < KeyHash.keySize kind, source.memaddrs (panByteAlignHOL (width := 64) (byteAddress query offset)))
    (owned : property value)
    (threshold : old.capacity < 2 * slots.length + 2)
    (heap : source.globals.lookup (ofString "heap_ptr") = some (.val (.word (BitVec.ofNat 64 start))))
    (bits : Nat) (power : old.capacity = 2 ^ bits) (minimum : 2 ≤ bits)
    (allocCode : source.code.lookup (ofString "alloc") = some (PersistentAlloc.formals, PersistentAlloc.body, .one))
    (zeroCode : source.code.lookup (ofString "memzero") = some (Zero.formals, Zero.body, .one))
    (hashCode : source.code.lookup (ofString "htab_hash") = some (Hash.formals, Hash.body, .one))
    (copyCode : source.code.lookup (ofString "memcpy") = some (CopyGeneral.formals, Copy32.body, .one))
    (insertCode : source.code.lookup (ofString "htab_insert_raw") = some (TableCall.formals, Insert.body, .one))
    (growCode : source.code.lookup (ofString "htab_grow") = some (Grow.formals, Grow.body, .one))
    (enough : afterGrowPrice kind old.capacity slots.length ≤ source.clock) :
    ∃ paid memory target next, paid ≤ afterGrowPrice kind old.capacity slots.length ∧
      evaluateHOLFiniteState source afterPresent = (some (.returned (.val (.word 0#64))), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite (GrowRuntime.callState source kind old start memory paid) ∧
      next.length = slots.length + 1 ∧
      MemoryModel.Header memory kind (relocated kind (old.base .header) start (2 * old.capacity)) (BitVec.ofNat 64 next.length) ∧
      MemoryModel.Occupied target kind (relocated kind (old.base .header) start (2 * old.capacity)) next ∧
      TableFootprint.Frame source.memory memory kind (relocated kind (old.base .header) start (2 * old.capacity)) ∧
      Get.OccupiedValuesHave target (cell (relocated kind (old.base .header) start (2*old.capacity)) .values 0) (BitVec.ofNat 64 (2*old.capacity)) next property := by
  have countBound := MemoryModel.Occupied.length_le source kind old slots occupied
  have guard := growth_read source kind old oldValid domain slots.length countBound header tableLocal threshold
  have args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) [localVar "t"] = some (Grow.values (cell old .header 0)) := by
    simp [Grow.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal]
  obtain ⟨growPaid, growMemory, grownSlots, growBound, grown, grownLength, grownHeader, grownModel, _, growFootprint, growValues⟩ := GrowRuntime.call_execute_values source kind old oldValid start newValid earlier domain little slots header occupied property values heap bits power minimum
    allocCode zeroCode hashCode copyCode insertCode growCode [localVar "t"] args (by dsimp only [afterGrowPrice] at enough; omega)
  let grownState := GrowRuntime.callState source kind old start growMemory growPaid
  have growing : evaluateHOLFiniteState source (.ite growthTest growCall .skip) = (none, grownState) := by
    simp only [eval] at guard
    simp only [evaluateHOLFiniteState_ite, guard, show (1#64 : BitVec 64) ≠ 0#64 from by decide, ↓reduceIte]
    exact grown
  have insertArgs : evalListHOLFinite grownState (h := fun address => Classical.propDecidable (grownState.memaddrs address))
      [localVar "t", localVar "key", localVar "value"] = some (TableCall.values (cell old .header 0) query value) := by
    simp [TableCall.values, evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, tableLocal, keyLocal, valueLocal, grownState, GrowRuntime.callState]
  obtain ⟨newSmall, newPower, _⟩ := MemoryModel.growth_shape kind old oldValid bits power minimum
  have room : grownSlots.length < 2 * old.capacity := by have positive := oldValid.positive; omega
  obtain ⟨insertPaid, index, insertBound, inside, fresh, inserted, nextHeader, nextModel⟩ := MemoryModel.insertion_call grownState kind _ newValid domain little grownSlots room grownHeader grownModel query value
    (bits + 1) newSmall newPower queryFits queryMapped hashCode copyCode insertCode [localVar "t", localVar "key", localVar "value"] insertArgs
    (by change grownSlots.length + KeyHash.hashPrice kind + MemeqByteRuntime.price (KeyHash.keySize kind) + 2 ≤ source.clock - growPaid; dsimp only [afterGrowPrice] at enough; omega)
  let memory := MemoryModel.insertedMemory growMemory source.be kind (relocated kind (old.base .header) start (2 * old.capacity)) query index (BitVec.ofNat 64 grownSlots.length) value
  let post := {grownState with memory := memory, clock := grownState.clock - insertPaid}
  have returned : evaluateHOLFiniteState post Insert.returnZero = (some (.returned (.val (.word 0#64))), emptyLocalsHOLFinite post) := by
    simp [Insert.returnZero, evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
  refine ⟨growPaid + insertPaid, memory, emptyLocalsHOLFinite post, grownSlots ++ [index.toNat], ?_, ?_, ?_, ?_, nextHeader, ?_, ?_, ?_⟩
  · dsimp only [afterGrowPrice]
    omega
  · rw [afterPresent, StateSteps.next_sequence source grownState _ _ growing (by change source.clock - growPaid ≤ source.clock; omega),
      StateSteps.next_sequence grownState post insertCall Insert.returnZero inserted (Nat.sub_le _ _)]
    exact returned
  · change emptyLocalsHOLFinite {source with globals := _, memory := memory, clock := source.clock - growPaid - insertPaid} = _
    have subtract : source.clock - growPaid - insertPaid = source.clock - (growPaid + insertPaid) := by omega
    rw [subtract]
    rfl
  · simp only [List.length_append, List.length_singleton, grownLength]
  · exact MemoryModel.Occupied.of_fields _ _ kind _ _ nextModel rfl rfl rfl
  · have countInside : (BitVec.ofNat 64 grownSlots.length).toNat < 2 * old.capacity := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind _ newValid))]
      exact room
    exact TableFootprint.Frame.trans source.memory growMemory memory kind _ growFootprint
      (TableFootprint.inserted growMemory source.be kind _ newValid query index _ value inside countInside)

  · have countInside : (BitVec.ofNat 64 grownSlots.length).toNat < 2 * old.capacity := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.lt_trans room (capacity_small kind _ newValid))]
      exact room
    exact MemoryModel.values_after_insert grownState kind _ newValid query index _ value inside countInside grownSlots property growValues owned

end InitECandidate.Solver.MutableTable.Set

#print axioms InitECandidate.Solver.MutableTable.Set.after_grow_values
