import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordCounter
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def advanced (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (index : Fin 16) :=
  QueryBranch.bind (QueryBranch.bind
    {source with memory:=StoreWord.put source.memory (record+32#64) (BitVec.ofNat 64 index.val)}
    "slot" (BitVec.ofNat 64 index.val)) "mode" 2#64

/-- Execute the original continuing-branch index/slot/mode update. The
incoming physical descriptor may already contain the just-updated OCC,
while I is still the previous index until this actual store. -/
theorem branch_advance_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db oldSlot oldMode : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (view : WitnessRecord.View source record db data)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word oldSlot)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode))) :
    evaluateHOLFiniteState source branchAdvance=(none,advanced source record index) := by
  let indexed : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (record+32#64) (BitVec.ofNat 64 index.val)}
  let slotState:=QueryBranch.bind indexed "slot" (BitVec.ofNat 64 index.val)
  have mapped : source.memaddrs (record+32#64):=by simpa only [byteAddress] using view.mapped source record db data 32 (by decide) (by decide)
  have addressRead : eval source (.op .add [localVar "top",.const 32#64])=some (.val (.word (record+32#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have indexRead : eval source (localVar "i")=some (.val (.word (BitVec.ofNat 64 index.val))):=by
    simp [eval,evalHOLExact,localVar,toExact,indexCell]
  have storeRun:=StoreWord.execute source (.op .add [localVar "top",.const 32#64]) (localVar "i") (record+32#64) (BitVec.ofNat 64 index.val) addressRead indexRead mapped
  change evaluateHOLFiniteState source (writeAt "top" 32#64 (localVar "i"))=(none,indexed) at storeRun
  have currentIndex : indexed.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))):=indexCell
  have currentRead : eval indexed (localVar "i")=some (.val (.word (BitVec.ofNat 64 index.val))):=by
    simp [eval,evalHOLExact,localVar,toExact,currentIndex]
  have slotRun:=StateSteps.assign_execute indexed "slot" (localVar "i") oldSlot (BitVec.ofNat 64 index.val) slotCell currentRead
  have currentMode : slotState.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=
    (bind_lookup_other indexed "slot" "mode" _ (by decide)).trans modeCell
  have modeRun:=StateSteps.assign_execute slotState "mode" (.const 2#64) oldMode 2#64 currentMode rfl
  rw [branch_advance_shape,StateSteps.next_sequence _ _ _ _ storeRun (Nat.le_refl _),
    StateSteps.next_sequence _ _ _ _ slotRun (Nat.le_refl _),modeRun]
  rfl

theorem advanced_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : WitnessRecord.Description) (oldIndex index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node oldIndex occupied) :
    WitnessRecord.View (advanced source record index) record db ((WitnessRecord.BranchCounter.index index).description data node oldIndex occupied) :=
  (view.branch_counter source record db node data oldIndex occupied (.index index) payload).of_fields _ _ record db _ rfl rfl

theorem advanced_fields (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (index : Fin 16) :
    let current:=advanced source record index
    current.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 index.val))) ∧
      current.locals.lookup (ofString "mode")=some (.val (.word 2#64)) ∧
      current.memory (record+32#64)=.word (BitVec.ofNat 64 index.val) ∧ current.globals=source.globals ∧ current.clock=source.clock :=
  ⟨(bind_lookup_other _ "mode" "slot" 2#64 (by decide)).trans (bind_lookup_same _ _ _),bind_lookup_same _ _ _,if_pos rfl,rfl,rfl⟩

theorem advanced_other (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record : BitVec 64) (index : Fin 16)
    (name : String) (notSlot : ofString "slot"≠ofString name) (notMode : ofString "mode"≠ofString name) :
    (advanced source record index).locals.lookup (ofString name)=source.locals.lookup (ofString name) :=
  (bind_lookup_other _ "mode" name 2#64 notMode).trans (bind_lookup_other _ "slot" name (BitVec.ofNat 64 index.val) notSlot)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_advance_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.advanced_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.advanced_fields
#print axioms InitECandidate.Solver.Mpt.WitnessCore.advanced_other
