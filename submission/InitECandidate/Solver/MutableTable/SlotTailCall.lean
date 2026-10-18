import InitECandidate.Solver.MutableTable.SlotCall

namespace InitECandidate.Solver.MutableTable.Slot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString

/-- Original tail-call form used by htab_item, with one caller clock. -/
theorem tail_call (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (index : Nat) (inside : index < plan.capacity)
    (code : source.code.lookup (ofString "htab_slot") = some (formals, body, tripleShape))
    (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.values (cell plan .header 0) (BitVec.ofNat 64 index)))
    (enough : 1 ≤ source.clock) :
    ∃ value target, evaluateHOLFiniteState source (.call none (ofString "htab_slot") arguments) =
      (some (.returned (triple (if index ∈ slots then 1#64 else 0#64) (cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)) value)), target) ∧
      emptyLocalsHOLFinite target = emptyLocalsHOLFinite {source with clock := source.clock - 1} := by
  obtain ⟨callee, called, tableLocal, indexLocal⟩ := ReadCall.environment source.code.lookup (ofString "htab_slot") body tripleShape "i" (by decide) (cell plan .header 0) (BitVec.ofNat 64 index) code
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨value, target, actual, frame⟩ := execute entry kind plan valid domain slots entryModel header index inside tableLocal indexLocal
  have calledRun := evaluateHOLFiniteState_call_return_none source
    (triple (if index ∈ slots then 1#64 else 0#64) (cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)) value)
    (ofString "htab_slot") arguments _ body callee tripleShape target args called (by omega) actual
    (by simp [triple, tripleShape, shapeOfHOLExact, shapeEqHOL_eq_true])
  exact ⟨value, emptyLocalsHOLFinite target, calledRun, frame⟩

end InitECandidate.Solver.MutableTable.Slot

#print axioms InitECandidate.Solver.MutableTable.Slot.tail_call
