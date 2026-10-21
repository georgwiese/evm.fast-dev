import InitECandidate.Solver.Mpt.WitnessCoreReturnProgram
import InitECandidate.Solver.Mpt.WitnessRecordCounter
import InitECandidate.Solver.WitnessRadix.StateSteps

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def occupiedNext (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (child : BitVec 64) : Fin 17:=
  if child=0#64 then occupied else ⟨occupied.val+1,by have bound:=index.isLt; omega⟩
def occupancyState (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record child : BitVec 64) (occupied : Fin 17) : PanSemStateFiniteExact 64 Guest.HostMemory:=
  if child=0#64 then source else {source with memory:=StoreWord.put source.memory (record+40#64) (BitVec.ofNat 64 (occupied.val+1))}

theorem occupancy_write_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record))) :
    evaluateHOLFiniteState source branchOccupancyWrite=
      (none,{source with memory:=StoreWord.put source.memory (record+40#64) (BitVec.ofNat 64 (occupied.val+1))}) := by
  have mapped : source.memaddrs (record+40#64):=by simpa only [byteAddress] using view.mapped source record db data 40 (by decide) (by decide)
  have cell : source.memory (record+40#64)=.word (BitVec.ofNat 64 occupied.val):=
    view.cells (40,BitVec.ofNat 64 occupied.val) (by simp [WitnessRecord.Description.cells,payload])
  have addressRead : eval source (.op .add [localVar "top",.const 40#64])=some (.val (.word (record+40#64))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp]
  have valueRead : eval source (.op .add [readAt "top" 40#64,.const 1#64])=some (.val (.word (BitVec.ofNat 64 (occupied.val+1)))):=by
    simp [eval,readAt,evalHOLExact,evalListHOLExact,localVar,toExact,topCell,valueIsWord,valueWord,wordOpHOL,wordOp,memLoadHOLExact,isWfShapeExactHOL,mapped,cell,BitVec.ofNat_add]
  exact StoreWord.execute source _ _ (record+40#64) _ addressRead valueRead mapped

theorem occupancy_choice_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    evaluateHOLFiniteState source (.ite (.cmp .notEqual (localVar "result") (.const 0#64)) branchOccupancyWrite .skip)=
      (none,occupancyState source record child occupied) := by
  have choice : evaluateHOLFiniteState source (.ite (.cmp .notEqual (localVar "result") (.const 0#64)) branchOccupancyWrite .skip)=
      if child=0#64 then (none,source) else evaluateHOLFiniteState source branchOccupancyWrite:=by
    by_cases zero : child=0#64 <;>
      simp [evaluateHOLFiniteState_ite,evalHOLExact,localVar,toExact,resultCell,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,evaluateHOLFiniteState_skip]
  rw [choice]
  by_cases zero : child=0#64
  · rw [if_pos zero,occupancyState,if_pos zero]
  · rw [if_neg zero,occupancyState,if_neg zero]
    exact occupancy_write_execute source record db node data index occupied view payload topCell

theorem occupancy_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied) :
    WitnessRecord.View (occupancyState source record child occupied) record db
      ((WitnessRecord.BranchCounter.occupied (occupiedNext index occupied used child)).description data node index occupied) := by
  by_cases zero : child=0#64
  · simp only [occupancyState,occupiedNext,if_pos zero]
    have same : (WitnessRecord.BranchCounter.occupied occupied).description data node index occupied=data:=by
      simp only [WitnessRecord.BranchCounter.description,WitnessRecord.BranchCounter.nextIndex,WitnessRecord.BranchCounter.nextOccupied]
      rw [←payload]
    rw [same]
    exact view
  · simpa only [occupancyState,occupiedNext,if_neg zero,WitnessRecord.BranchCounter.offset,WitnessRecord.BranchCounter.word] using
      view.branch_counter source record db node data index occupied (.occupied (occupiedNext index occupied used child)) payload

theorem after_child_trace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    evaluateHOLFiniteState source branchAfterChild=evaluateHOLFiniteState (occupancyState source record child occupied) branchAfterOccupancy := by
  have run:=occupancy_choice_execute source record db node child data index occupied view payload topCell resultCell
  have clock : (occupancyState source record child occupied).clock≤source.clock:=by
    unfold occupancyState
    split <;> exact Nat.le_refl _
  rw [branch_after_child_shape,StateSteps.next_sequence source _ _ _ run clock]

theorem index_increment_execute (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Fin 16)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val)))) :
    evaluateHOLFiniteState source (.assign .local (ofString "i") (.op .add [localVar "i",.const 1#64]))=
      (none,QueryBranch.bind source "i" (BitVec.ofNat 64 (index.val+1))) := by
  have read : eval source (.op .add [localVar "i",.const 1#64])=some (.val (.word (BitVec.ofNat 64 (index.val+1)))):=by
    simp [eval,evalHOLExact,evalListHOLExact,localVar,toExact,indexCell,valueIsWord,valueWord,wordOpHOL,wordOp,BitVec.ofNat_add]
  exact StateSteps.assign_execute source "i" _ _ _ indexCell read

theorem after_occupancy_trace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Fin 16)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val)))) :
    evaluateHOLFiniteState source branchAfterOccupancy=
      evaluateHOLFiniteState (QueryBranch.bind source "i" (BitVec.ofNat 64 (index.val+1))) branchIndexChoice := by
  rw [branch_after_occupancy_shape,StateSteps.next_sequence source _ _ _ (index_increment_execute source index indexCell) (Nat.le_refl _)]

/-- The actual source comparison is signed. The real Fin16 counter gives
a nonnegative next value<=16, so its result is the precise natural test. -/
theorem branch_index_choice (source : PanSemStateFiniteExact 64 Guest.HostMemory) (index : Fin 16)
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 (index.val+1))))) :
    evaluateHOLFiniteState source branchIndexChoice=
      if index.val+1<16 then evaluateHOLFiniteState source branchAdvance else evaluateHOLFiniteState source branchFinish := by
  have bound:=index.isLt
  have number : (BitVec.ofNat 64 (index.val+1)).toNat=index.val+1:=by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have sign : index.val+1<9223372036854775808:=by omega
  have test : eval source (.cmp .less (localVar "i") (.const 16#64))=
      some (.val (.word (if index.val+1<16 then 1#64 else 0#64))):=by
    simp [eval,evalHOLExact,localVar,toExact,indexCell,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      Flapjack.Compiler.Encoders.Asm.holAsmSignedLess,number,sign,show ¬9223372036854775808≤index.val+1 from by omega]
  rw [branch_index_choice_shape,evaluateHOLFiniteState_ite]
  simp only [eval] at test
  rw [test]
  by_cases inside : index.val+1<16 <;> simp [inside]

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.occupancy_write_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.occupancy_choice_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.occupancy_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_child_trace
#print axioms InitECandidate.Solver.Mpt.WitnessCore.index_increment_execute
#print axioms InitECandidate.Solver.Mpt.WitnessCore.after_occupancy_trace
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_index_choice
