import InitECandidate.Solver.Mpt.WitnessCoreDecodeProgram
import InitECandidate.Solver.Mpt.WitnessRecordLink
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def pushedSlot (payload : WitnessRecord.Payload) : BitVec 64:=if payload.stage=1#64 then 1#64 else 0#64
def pushed (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record previous : BitVec 64) (payload : WitnessRecord.Payload) :=
  bind (bind (bind {source with memory:=StoreWord.put source.memory record previous} "top" record) "slot" (pushedSlot payload)) "mode" 2#64

private theorem slot_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db oldSlot : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot))) :
    evaluateHOLFiniteState source pushSlot=(none,bind source "slot" (pushedSlot data.payload)) := by
  have mapped : source.memaddrs (record+8#64):=by
    simpa only [byteAddress] using view.mapped source record db data 8 (by decide) (by decide)
  have stored:=view.stage source record db data
  have read : eval source pushStageTest=some (.val (.word (if data.payload.stage=1#64 then 1#64 else 0#64))):=by
    simp [eval,pushStageTest,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,
      valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,stored,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have choice : evaluateHOLFiniteState source pushSlot=
      if data.payload.stage=1#64 then evaluateHOLFiniteState source (.assign .local (ofString "slot") (.const 1#64))
      else evaluateHOLFiniteState source (.assign .local (ofString "slot") (.const 0#64)):=by
    rw [pushSlot,evaluateHOLFiniteState_ite]
    simp only [eval] at read
    rw [read]
    by_cases selected : data.payload.stage=1#64 <;> simp [selected]
  rw [choice]
  by_cases selected : data.payload.stage=1#64
  · rw [if_pos selected]
    simpa only [pushedSlot,if_pos selected] using StateSteps.assign_execute source "slot" (.const 1#64) oldSlot 1#64 slotCell rfl
  · rw [if_neg selected]
    simpa only [pushedSlot,if_neg selected] using StateSteps.assign_execute source "slot" (.const 0#64) oldSlot 0#64 slotCell rfl

/-- Execute the actual original core's complete record push: derive the
mapped PREV store from the real record view, read its actual stage, then set
the genuine top/slot/resolve-mode locals. No future store/read is assumed. -/
theorem push_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db previous oldSlot oldMode : BitVec 64) (data : WitnessRecord.Description)
    (view : WitnessRecord.View source record db data)
    (decodedCell : source.locals.lookup (ofString "d")=some (.rStruct [.val (.word 1#64),.val (.word record)]))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word previous)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source decodePush=(none,pushed source record previous data.payload) := by
  let linked : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory record previous}
  let topState:=bind linked "top" record
  let slotState:=bind topState "slot" (pushedSlot data.payload)
  have addressRead : eval source (.op .add [decodeField 1,.const 0#64])=some (.val (.word record)):=by
    simp [eval,decodeField,evalHOLExact,evalListHOLExact,localVar,toExact,decodedCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have previousRead : eval source (localVar "top")=some (.val (.word previous)):=by
    simp [eval,evalHOLExact,localVar,toExact,topCell]
  have mapped : source.memaddrs record:=by
    simpa only [byteAddress,BitVec.add_zero] using view.mapped source record db data 0 (by decide) (by decide)
  have linkRun:=StoreWord.execute source (.op .add [decodeField 1,.const 0#64]) (localVar "top") record previous addressRead previousRead mapped
  change evaluateHOLFiniteState source pushLink=(none,linked) at linkRun
  have linkedDecoded : linked.locals.lookup (ofString "d")=some (.rStruct [.val (.word 1#64),.val (.word record)]):=decodedCell
  have topRead : eval linked (decodeField 1)=some (.val (.word record)):=by
    simp [eval,decodeField,evalHOLExact,localVar,toExact,linkedDecoded]
  have topRun:=StateSteps.assign_execute linked "top" (decodeField 1) previous record topCell topRead
  change evaluateHOLFiniteState linked pushTop=(none,topState) at topRun
  have linkedView:=view.linked source record db previous data
  have topView:=linkedView.of_fields linked topState record db data rfl rfl
  have currentSlot : topState.locals.lookup (ofString "slot")=some (.val (.word oldSlot)):=
    (bind_lookup_other linked "top" "slot" record (by decide)).trans slotCell
  have slotRun:=slot_execute topState record db oldSlot data topView (bind_lookup_same _ _ _) currentSlot
  have topMode : topState.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other linked "top" "mode" record (by decide)).trans modeCell
  have currentMode : slotState.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other topState "slot" "mode" (pushedSlot data.payload) (by decide)).trans topMode
  have modeRun:=StateSteps.assign_execute slotState "mode" (.const 2#64) oldMode 2#64 currentMode rfl
  change evaluateHOLFiniteState slotState pushMode=(none,pushed source record previous data.payload) at modeRun
  rw [push_shape,StateSteps.next_sequence source linked pushLink _ linkRun (Nat.le_refl _),
    StateSteps.next_sequence linked topState pushTop _ topRun (Nat.le_refl _),
    StateSteps.next_sequence topState slotState pushSlot pushMode slotRun (Nat.le_refl _),modeRun]

theorem pushed_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db previous : BitVec 64)
    (data : WitnessRecord.Description) (view : WitnessRecord.View source record db data) :
    WitnessRecord.View (pushed source record previous data.payload) record db data :=
  (view.linked source record db previous data).of_fields _ _ record db data rfl rfl

theorem pushed_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record previous : BitVec 64) (payload : WitnessRecord.Payload) :
    let current:=pushed source record previous payload
    current.locals.lookup (ofString "top")=some (.val (.word record)) ∧
      current.locals.lookup (ofString "slot")=some (.val (.word (pushedSlot payload))) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧
      current.memory record=.word previous ∧ current.globals=source.globals ∧ current.clock=source.clock := by
  let linked : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory record previous}
  let topState:=bind linked "top" record
  let slotState:=bind topState "slot" (pushedSlot payload)
  have top : slotState.locals.lookup (ofString "top")=some (.val (.word record)):=
    (bind_lookup_other topState "slot" "top" _ (by decide)).trans (bind_lookup_same _ _ _)
  exact ⟨(bind_lookup_other slotState "mode" "top" 2#64 (by decide)).trans top,
    (bind_lookup_other slotState "mode" "slot" 2#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,if_pos rfl,rfl,rfl⟩

theorem pushed_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record previous : BitVec 64) (payload : WitnessRecord.Payload)
    (name : String) (notTop : ofString "top"≠ofString name) (notSlot : ofString "slot"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (pushed source record previous payload).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "mode" name 2#64 notMode).trans
    ((bind_lookup_other _ "slot" name _ notSlot).trans (bind_lookup_other _ "top" name record notTop))

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.push_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.pushed_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.pushed_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.pushed_other
