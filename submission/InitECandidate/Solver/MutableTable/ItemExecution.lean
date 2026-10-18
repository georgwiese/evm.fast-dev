import InitECandidate.Solver.MutableTable.ItemProgram

namespace InitECandidate.Solver.MutableTable.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual dense-order item body, including the real order read and slot
tail call. A valid ordinal returns a used slot and preserves nonlocal state. -/
theorem execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (ordinal : Fin slots.length)
    (tableLocal : source.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))))
    (ordinalLocal : source.locals.lookup (ofString "ordinal") = some (.val (.word (BitVec.ofNat 64 ordinal.val))))
    (slotCode : source.code.lookup (ofString "htab_slot") = some (Slot.formals, Slot.body, Slot.tripleShape))
    (enough : 1 ≤ source.clock) :
    ∃ value target, evaluateHOLFiniteState source body = (some (.returned (Slot.triple 1#64
      (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  have countBound := MemoryModel.Occupied.length_le source kind plan slots occupied
  have ordinalInside : ordinal.val < plan.capacity := Nat.lt_of_lt_of_le ordinal.isLt countBound
  have orderHeader := MemoryModel.Header.read source kind plan valid domain _ header tableLocal 56 (by decide) (by decide) (cell plan .order 0) (by simp [MemoryModel.headerEntries])
  have orderMapped : source.memaddrs (cell plan .order 0 + BitVec.ofNat 64 ordinal.val * 8#64) := by
    rw [Delete.Move.natural_word_address kind plan valid .order ordinal.val ordinalInside, domain]
    exact mapped kind plan valid .order _ (by change 8 * ordinal.val < 8 * plan.capacity; omega) (by omega)
  have orderStored : source.memory (cell plan .order 0 + BitVec.ofNat 64 ordinal.val * 8#64) = .word (BitVec.ofNat 64 (slots.get ordinal)) := by
    rw [Delete.Move.natural_word_address kind plan valid .order ordinal.val ordinalInside]
    exact occupied.order ordinal
  have indexReadRun : eval source indexRead = some (.val (.word (BitVec.ofNat 64 (slots.get ordinal)))) := by
    simp only [eval] at orderHeader
    simp [eval, indexRead, localVar, evalHOLExact, evalListHOLExact, toExact, orderHeader, ordinalLocal, valueIsWord, valueWord, wordOpHOL, wordOp, panOpHOL,
      memLoadHOLExact, isWfShapeExactHOL, orderMapped, orderStored]
  let entered := bind source "i" (BitVec.ofNat 64 (slots.get ordinal))
  have entryT : entered.locals.lookup (ofString "t") = some (.val (.word (cell plan .header 0))) := (bind_lookup_other _ "i" "t" _ (by decide)).trans tableLocal
  have entryI : entered.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (slots.get ordinal)))) := bind_lookup_same _ _ _
  have args : evalListHOLFinite entered (h := fun address => Classical.propDecidable (entered.memaddrs address)) [localVar "t", localVar "i"] = some (ReadCall.values (cell plan .header 0) (BitVec.ofNat 64 (slots.get ordinal))) := by
    simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, toExact, localVar, entryT, entryI, ReadCall.values]
  have entryModel := MemoryModel.Occupied.of_fields source entered kind plan slots occupied rfl rfl rfl
  obtain ⟨value, target, actual, frame⟩ := Slot.tail_call entered kind plan valid domain slots entryModel header (slots.get ordinal)
    (occupied.inside _ (List.get_mem slots ordinal)) slotCode _ args enough
  have returned : evaluateHOLFiniteState entered (.call none (ofString "htab_slot") [localVar "t", localVar "i"]) =
      (some (.returned (Slot.triple 1#64 (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value)), target) := by
    simpa only [if_pos (List.get_mem slots ordinal)] using actual
  have scopeRun := Input.ScalarScope.declare_execute source target "i" indexRead (BitVec.ofNat 64 (slots.get ordinal)) _ _ indexReadRun returned
  refine ⟨value, restore source "i" target, ?_, frame⟩
  rw [body_shape]
  exact scopeRun

end InitECandidate.Solver.MutableTable.Item

#print axioms InitECandidate.Solver.MutableTable.Item.execute
