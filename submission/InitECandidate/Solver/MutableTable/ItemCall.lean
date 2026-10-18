import InitECandidate.Solver.MutableTable.ItemExecution

namespace InitECandidate.Solver.MutableTable.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Whole original item caller, with exactly two source caller clocks. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (ordinal : Fin slots.length)
    (slotCode : source.code.lookup (ofString "htab_slot") = some (Slot.formals, Slot.body, Slot.tripleShape))
    (itemCode : source.code.lookup (ofString "htab_item") = some (formals, body, Slot.tripleShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.values (cell plan .header 0) (BitVec.ofNat 64 ordinal.val)))
    (enough : 2 ≤ source.clock) :
    ∃ value, evaluateHOLFiniteState source (.decCall (ofString name) Slot.tripleShape (ofString "htab_item") arguments continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Slot.triple 1#64
        (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value) {source with clock := source.clock - 2}) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, tableLocal, ordinalLocal⟩ := ReadCall.environment source.code.lookup (ofString "htab_item") body Slot.tripleShape "ordinal" (by decide) (cell plan .header 0) (BitVec.ofNat 64 ordinal.val) itemCode
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨value, target, actual, frame⟩ := execute entry kind plan valid domain slots entryModel header ordinal tableLocal ordinalLocal slotCode (by change 1 ≤ source.clock - 1; omega)
  have caller := pure_value_call source target name (ofString "htab_item") Slot.tripleShape Slot.tripleShape arguments _ body continuation callee
    (Slot.triple 1#64 (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value) 1 args called (by omega) actual
    (by simp [Slot.triple, Slot.tripleShape, shapeOfHOLExact, shapeEqHOL_eq_true]) frame
  refine ⟨value, ?_⟩
  have subtract : source.clock - 1 - 1 = source.clock - 2 := by omega
  simpa only [subtract] using caller

end InitECandidate.Solver.MutableTable.Item

#print axioms InitECandidate.Solver.MutableTable.Item.call_execute
