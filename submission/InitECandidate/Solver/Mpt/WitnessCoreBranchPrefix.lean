import InitECandidate.Solver.Mpt.WitnessCoreBranchChild
import InitECandidate.Solver.Mpt.WitnessCoreBranchCounters
import InitECandidate.Solver.Mpt.WitnessRecordFrame

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

def branchCounterEntry (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node child : BitVec 64) (index : Fin 16) (occupied : Fin 17) :=
  QueryBranch.bind (occupancyState {source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child} record child occupied)
    "i" (BitVec.ofNat 64 (index.val+1))

theorem occupied_next_bound (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val) (child : BitVec 64) :
    (occupiedNext index occupied used child).val≤index.val+1 := by
  unfold occupiedNext
  split
  · exact used.trans (Nat.le_succ _)
  · exact Nat.succ_le_succ used

/-- Follow the genuine child store, conditional OCC increment and local
i increment to the real signed index choice. It either continues to the
actual next-slot update or enters the real final-value parser prefix, with
the same physical updated record and rows. -/
theorem branch_children_trace (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (branchCell : source.locals.lookup (ofString "br")=some (.val (.word node)))
    (indexCell : source.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word child))) :
    let ready:=branchCounterEntry source record node child index occupied
    evaluateHOLFiniteState source branchChildren=
      if index.val+1<16 then evaluateHOLFiniteState ready branchAdvance else evaluateHOLFiniteState ready branchFinish := by
  let childState : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child}
  let occupiedState:=occupancyState childState record child occupied
  let ready:=branchCounterEntry source record node child index occupied
  have childRun:=branch_child_execute source record db node child data index occupied view payload branchCell indexCell resultCell
  have childView:=view.branch_child source record db node child data index occupied payload
  have currentIndex : occupiedState.locals.lookup (ofString "i")=some (.val (.word (BitVec.ofNat 64 index.val))):=by
    unfold occupiedState occupancyState
    split <;> exact indexCell
  have indexChoice:=branch_index_choice ready index (bind_lookup_same _ _ _)
  change evaluateHOLFiniteState source branchChildren=
    if index.val+1<16 then evaluateHOLFiniteState ready branchAdvance else evaluateHOLFiniteState ready branchFinish
  rw [branch_children_shape,StateSteps.next_sequence source childState _ _ childRun (Nat.le_refl _),
    after_child_trace childState record db node child data index occupied childView payload topCell resultCell,
    after_occupancy_trace occupiedState index currentIndex]
  change evaluateHOLFiniteState ready branchIndexChoice=_
  exact indexChoice

theorem branch_counter_entry_view (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node child : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17) (used : occupied.val≤index.val)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied) :
    WitnessRecord.View (branchCounterEntry source record node child index occupied) record db
      ((WitnessRecord.BranchCounter.occupied (occupiedNext index occupied used child)).description data node index occupied) := by
  let childState : PanSemStateFiniteExact 64 Guest.HostMemory:={source with memory:=StoreWord.put source.memory (WitnessRecord.childAddress node index) child}
  let occupiedState:=occupancyState childState record child occupied
  have childView:=view.branch_child source record db node child data index occupied payload
  have occupiedView:=occupancy_view childState record db node child data index occupied used childView payload
  exact occupiedView.of_fields occupiedState (branchCounterEntry source record node child index occupied) record db _ rfl rfl

theorem branch_counter_entry_memory (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node child : BitVec 64)
    (index : Fin 16) (occupied : Fin 17) (query : BitVec 64)
    (notChild : query≠WitnessRecord.childAddress node index) (notOccupied : query≠record+40#64) :
    (branchCounterEntry source record node child index occupied).memory query=source.memory query := by
  by_cases zero : child=0#64 <;> simp [branchCounterEntry,occupancyState,zero,QueryBranch.bind,setVarHOLFinite,StoreWord.put,notChild,notOccupied]

theorem branch_counter_entry_local (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record node child : BitVec 64)
    (index : Fin 16) (occupied : Fin 17) (name : String) (other : ofString "i"≠ofString name) :
    (branchCounterEntry source record node child index occupied).locals.lookup (ofString name)=source.locals.lookup (ofString name) := by
  rw [branchCounterEntry,bind_lookup_other _ "i" name _ other]
  unfold occupancyState
  split <;> rfl

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.occupied_next_bound
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_children_trace
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_counter_entry_view
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_counter_entry_memory
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_counter_entry_local
