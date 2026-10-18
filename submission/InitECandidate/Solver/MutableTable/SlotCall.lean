import InitECandidate.Solver.MutableTable.SlotExecution
import InitECandidate.Solver.MutableTable.ReadCallEnvironment

namespace InitECandidate.Solver.MutableTable.Slot
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- Actual scoped slot caller with its one caller clock and full tuple ABI. -/
theorem call_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (index : Nat) (inside : index < plan.capacity)
    (code : source.code.lookup (ofString "htab_slot") = some (formals, body, tripleShape))
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun address => Classical.propDecidable (source.memaddrs address)) arguments = some (ReadCall.values (cell plan .header 0) (BitVec.ofNat 64 index)))
    (enough : 1 ≤ source.clock) :
    ∃ value, evaluateHOLFiniteState source (.decCall (ofString name) tripleShape (ofString "htab_slot") arguments continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString name)
        (triple (if index ∈ slots then 1#64 else 0#64) (cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)) value)
        {source with clock := source.clock - 1}) continuation
       (output.1, restore source name output.2)) := by
  obtain ⟨callee, called, tableLocal, indexLocal⟩ := ReadCall.environment source.code.lookup (ofString "htab_slot") body tripleShape "i" (by decide)
    (cell plan .header 0) (BitVec.ofNat 64 index) code
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨value, target, actual, frame⟩ := execute entry kind plan valid domain slots entryModel header index inside tableLocal indexLocal
  refine ⟨value, ?_⟩
  have caller := pure_value_call source target name (ofString "htab_slot") tripleShape tripleShape arguments _ body continuation callee
    (triple (if index ∈ slots then 1#64 else 0#64) (cell plan .keys 0 + BitVec.ofNat 64 index * BitVec.ofNat 64 (stride kind)) value) 0 args called enough actual
    (by simp [triple, tripleShape, shapeOfHOLExact, shapeEqHOL_eq_true]) frame
  simpa only [Nat.sub_zero] using caller

end InitECandidate.Solver.MutableTable.Slot

#print axioms InitECandidate.Solver.MutableTable.Slot.call_execute
