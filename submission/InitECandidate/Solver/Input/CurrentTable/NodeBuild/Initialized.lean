import InitECandidate.Solver.Input.CurrentTable.NodeBuild.Loop
import InitECandidate.Solver.Input.ClockCostCurrent
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.CurrentTable.NodeBuild
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix QueryBranch

def loopEntry (data : Data) (source target : PanSemStateFiniteExact 64 Guest.HostMemory) :=
  bind (CallNormal.continuationEntry source target "t" (.val (.word data.table))) "i" 0#64

/-- Initialize the loop image from this same actual table-constructor
return. No uninitialized array word is interpreted as a live Patricia node. -/
theorem initialized (data : Data) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (returned : New.Returned source target data.table data.cap data.stp data.pad)
    (layout : Layout data) (little : source.be=false)
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (outCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out)))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word data.array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total)))) :
    State data (loopEntry data source target) (loopEntry data source target) 0 := by
  let entry := loopEntry data source target
  have inputFrame : HashInput.Frame source entry data.lower data.upper :=
    ⟨by intro query lower upper; exact returned.earlier query (by have := layout.inputBefore; omega)⟩
  have nextRows := rows.of_frame source entry data.array data.pointers data.lengths data.total data.lower data.upper inputFrame
  have tableCell := CallNormal.continuation_lookup_same source target "t" (.val (.word data.table))
  have nextArray := (CallNormal.continuation_lookup_other source target "t" "slice_arr" (.val (.word data.table)) (by decide)).trans arrayCell
  have nextCount := (CallNormal.continuation_lookup_other source target "t" "n" (.val (.word data.table)) (by decide)).trans countCell
  have heap : NormalHeapEffects.AtLeast (New.endPointer data.table data.cap).toNat entry :=
    ⟨New.endPointer data.table data.cap,returned.heapCell,Nat.le_refl _,returned.geometry.endBound,returned.geometry.endAligned⟩
  have image := (image_from_constructor returned (ValueOf data)).of_frame (target:=entry) rfl
  exact ⟨returned.arena.of_frame rfl,returned.metadata.2.1.trans little,returned.environment.of_frame rfl,
    (returned.globals (ofString "mpt_hash_scratch") (by decide)).trans outCell,nextRows,HashInput.Frame.refl entry _ _,heap,
    (fun _=>rfl),
    (bind_lookup_other _ "i" "slice_arr" _ (by decide)).trans nextArray,
    (bind_lookup_other _ "i" "n" _ (by decide)).trans nextCount,
    (bind_lookup_other _ "i" "t" _ (by decide)).trans tableCell,bind_lookup_same _ _ _,
    0#64,1,0,(fun _=>False),(fun _=>256),(fun _=>0#64),(fun _=>0#64),(fun _ _=>0#8),image,Nat.le_refl _⟩

/-- Once the actual constructor returns, every outcome of its original
insertion-loop continuation fits the actual row allowances. -/
theorem table_tail_cost (data : Data) (source target : PanSemStateFiniteExact 64 Guest.HostMemory)
    (returned : New.Returned source target data.table data.cap data.stp data.pad)
    (layout : Layout data) (little : source.be=false)
    (rows : Headers.Validate.Rows source data.array data.pointers data.lengths data.total data.lower data.upper)
    (outCell : source.globals.lookup (ofString "mpt_hash_scratch")=some (.val (.word data.out)))
    (arrayCell : source.locals.lookup (ofString "slice_arr")=some (.val (.word data.array)))
    (countCell : source.locals.lookup (ofString "n")=some (.val (.word (BitVec.ofNat 64 data.total)))) :
    target.clock-(evaluateHOLFiniteState (CallNormal.continuationEntry source target "t" (.val (.word data.table))) tableTail).2.clock≤remainingFrom data 0 := by
  let ready := CallNormal.continuationEntry source target "t" (.val (.word data.table))
  have initial := initialized data source target returned layout little rows outCell arrayCell countCell
  have front := loop_cost data (loopEntry data source target) (loopEntry data source target) 0 initial layout (by omega)
  have price := ClockCost.sequence_current (loopEntry data source target) loop returnTable (remainingFrom data 0) 0 front
    (ClockCost.returned ready.code _)
  have tailPrice := ClockCost.declared_current ready "i" (.const 0#64) 0#64 (.seq loop returnTable) (remainingFrom data 0) rfl
    (by simpa only [Nat.add_zero,loopEntry,ready] using price)
  rwa [←table_tail_shape] at tailPrice

end InitECandidate.Solver.Input.CurrentTable.NodeBuild

#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.initialized
#print axioms InitECandidate.Solver.Input.CurrentTable.NodeBuild.table_tail_cost
