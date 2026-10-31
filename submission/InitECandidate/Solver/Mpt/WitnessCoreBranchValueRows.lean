import InitECandidate.Solver.Mpt.WitnessCoreReturnCost
import InitECandidate.Solver.Mpt.WitnessCoreResolveRows
import InitECandidate.Solver.Input.ClockCostCurrent

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The original final-value arguments read row16 from the real arr2
binding, at physical offsets256/264 of the allocated17-row array. -/
theorem branch_value_arguments_read (source : PanSemStateFiniteExact 64 Guest.HostMemory) (array pointer : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem) (rows : WitnessDecode.Rows source array pointer bytes items)
    (selected : items[16]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr2")=some (.val (.word array))) :
    evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) branchValueArguments=
      some (Rlp.Header.values (Rlp.Slices.itemPointer pointer items 16) item.total) := by
  have inside : 16<items.length:=(List.getElem?_eq_some_iff.mp selected).choose
  have mapped:=AllocatedBytes.word_mapped source array (16*items.length) 256 rows.domain rows.allocation (by omega) rows.aligned (by decide)
  have lengthMapped:=AllocatedBytes.word_mapped source array (16*items.length) 264 rows.domain rows.allocation (by omega) rows.aligned (by decide)
  change source.memaddrs (array+256#64) at mapped
  change source.memaddrs (array+264#64) at lengthMapped
  have cells:=Rlp.Slices.Records.at source.memory array pointer items rows.records 16 item selected
  simp only [BitVec.add_assoc] at cells
  change source.memory (array+256#64)=.word (Rlp.Slices.itemPointer pointer items 16) ∧ source.memory (array+264#64)=.word item.total at cells
  simp [branchValueArguments,Rlp.Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,arrayCell,
    valueIsWord,valueWord,wordOpHOL,wordOp,panOpHOL,memLoadHOLExact,isWfShapeExactHOL,BitVec.add_assoc,mapped,lengthMapped,cells.1,cells.2]

/-- Every outcome of the whole original final-child arr2/item/tail block
is bounded using the current record's actual row16. Its real source slice
stays inside the original bounded parent input before the node database. -/
theorem branch_finish_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (record db node cursor limit : BitVec 64)
    (data : WitnessRecord.Description) (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source branchFinish).2.clock≤60*data.bytes+12 := by
  have inside : 16<data.items.length:=by have count:=view.count; rw [payload] at count; change data.items.length=17 at count; omega
  let item:=data.items[16]
  have selected : data.items[16]?=some item:=by simp [item,inside]
  have read : eval source (readAt "top" 24#64)=some (.val (.word data.array)):=resolve_array_read source record db data view topCell
  let ready:=QueryBranch.bind source "arr2" data.array
  have rows:=view.rows.frame source ready data.array data.listPointer data.bytes data.items rfl (fun _ _ _=>rfl)
  have args:=branch_value_arguments_read ready data.array data.listPointer data.bytes data.items item rows selected (bind_lookup_same _ _ _)
  obtain ⟨positive,small,lower,upper⟩:=view.rows.intervals 16 item selected
  have payloadUpper:=view.payloadUpper
  have before:=view.parentBeforeDb
  have fits : (Rlp.Slices.itemPointer data.listPointer data.items 16).toNat+item.total.toNat<2^64:=by have bound:=db.isLt; omega
  have priced:=branch_value_call_cost ready (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total cursor limit args
    (live.of_frame rfl) (arena.of_fields source ready cursor limit rfl rfl) fits installed
  have whole:=Input.ClockCost.declared_current source "arr2" (readAt "top" 24#64) data.array branchValueCall (60*item.total.toNat+12) read priced
  rw [branch_finish_shape]
  exact whole.trans (by omega)

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_arguments_read
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finish_cost
