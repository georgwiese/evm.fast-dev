import InitECandidate.Solver.MutableTable.ItemNormal
import InitECandidate.Solver.Input.ScopedCallSuccess

namespace InitECandidate.Solver.MutableTable.Item
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix NaturalLayout
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem scoped_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : KeyHash.Kind) (plan : Plan) (valid : Valid kind plan)
    (domain : source.memaddrs = InitE.ordinaryDomain) (slots : List Nat) (occupied : MemoryModel.Occupied source kind plan slots)
    (header : MemoryModel.Header source.memory kind plan (BitVec.ofNat 64 slots.length)) (ordinal : Fin slots.length)
    (installed : Input.OriginalCode.Installed source.code)
    (name : String) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (args : evalListHOLFinite source (h := fun query => Classical.propDecidable (source.memaddrs query)) arguments =
      some (ReadCall.values (cell plan .header 0) (BitVec.ofNat 64 ordinal.val)))
    (result : Option (PanSemResultExact 64)) (success : result = none ∨ ∃ value, result = some (.returned value))
    (normal : evaluateHOLFiniteState source (.decCall (ofString name) Slot.tripleShape (ofString "htab_item") arguments continuation) = (result,post)) :
    2 ≤ source.clock ∧ ∃ value inner,
      evaluateHOLFiniteState (setVarHOLFinite (ofString name) (Slot.triple 1#64
        (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value)
        {source with clock := source.clock - 2}) continuation = (result,inner) ∧
      post = restore source name inner := by
  obtain ⟨callee,called,tableLocal,ordinalLocal⟩ := ReadCall.environment source.code.lookup (ofString "htab_item") body Slot.tripleShape "ordinal" (by decide)
    (cell plan .header 0) (BitVec.ofNat 64 ordinal.val) (original_code source.code installed)
  obtain ⟨positive,target,returned,inner,bodyRun,checked,tailRun,scope⟩ := Input.CallNormal.scoped_success source post name Slot.tripleShape
    (ofString "htab_item") arguments _ body continuation callee Slot.tripleShape args called result success normal
  let entry := callEntryStateHOLFinite source callee
  have entryModel := MemoryModel.Occupied.of_fields source entry kind plan slots occupied rfl rfl rfl
  obtain ⟨funded,value,valueEq,fields⟩ := body_normal entry target kind plan valid domain slots entryModel header ordinal tableLocal ordinalLocal
    (slot_code source.code installed) returned bodyRun
  have restored := congrArg (fun state : PanSemStateFiniteExact 64 Guest.HostMemory => {state with locals := source.locals}) fields
  change {target with locals := source.locals} = {source with clock := source.clock - 1 - 1} at restored
  have subtract : source.clock - 1 - 1 = source.clock - 2 := by omega
  rw [subtract] at restored
  have canonical : Input.CallNormal.continuationEntry source target name returned = setVarHOLFinite (ofString name) (Slot.triple 1#64
      (cell plan .keys 0 + BitVec.ofNat 64 (slots.get ordinal) * BitVec.ofNat 64 (stride kind)) value) {source with clock := source.clock - 2} := by
    rw [valueEq]
    exact congrArg (setVarHOLFinite (ofString name) _) restored
  change 1 ≤ source.clock - 1 at funded
  rw [canonical] at tailRun
  exact ⟨by omega,value,inner,tailRun,scope⟩

end InitECandidate.Solver.MutableTable.Item

#print axioms InitECandidate.Solver.MutableTable.Item.scoped_normal
