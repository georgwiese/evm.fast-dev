import InitECandidate.Solver.Mpt.WitnessCoreBranchValueRows
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.Mpt.WitnessRecordFrame
import InitECandidate.Solver.Rlp.ItemCallNoneGlobalsNormal
import InitECandidate.Solver.Input.CallResumeLookup
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Mpt.WitnessCore
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- The real final-value call derives its item result and the actual
bv-bound continuation from a genuine normal caller. Its scratch parser
preserves the active record, row array and branch node. -/
theorem branch_value_call_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node heap cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (arrayCell : source.locals.lookup (ofString "arr2")=some (.val (.word data.array)))
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) (before : data.BeforeHeap heap.toNat)
    (recordAbove : cursor.toNat≤record.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchValueCall=(none,post)) :
    ∃ item : Rlp.ListItem, ∃ built header bytes flag inner,
      let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
      let ready:=Input.CallNormal.continuationEntry source built "bv" answer
      data.items[16]?=some item ∧ Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat answer ∧
      WitnessRecord.View ready record db data ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ Rlp.CurrentItem.Frame source ready ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧ ready.locals.lookup (ofString "bv")=some answer ∧
      evaluateHOLFiniteState ready afterBranchValue=(none,inner) ∧ post=restore source "bv" inner := by
  have inside : 16<data.items.length:=by
    have count:=view.count
    rw [payload] at count
    change data.items.length=17 at count
    omega
  let item:=data.items[16]
  have selected : data.items[16]?=some item:=by simp [item,inside]
  have args:=branch_value_arguments_read source data.array data.listPointer data.bytes data.items item view.rows selected arrayCell
  obtain ⟨positive,small,first,last⟩:=view.rows.intervals 16 item selected
  have payloadUpper:=view.payloadUpper
  have parentBefore:=view.parentBeforeDb
  have fits : (Rlp.Slices.itemPointer data.listPointer data.items 16).toNat+item.total.toNat<2^64:=by
    have bound:=db.isLt
    omega
  rw [branch_value_call_shape] at normal
  obtain ⟨funded,built,header,bytes,flag,inner,valid,nextArena,above,parserFrame,domain,endian,code,heapCell,globalCells,price,continued,endpoint⟩:=
    Rlp.Item.scoped_none_globals source post (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total cursor limit
      "bv" branchValueArguments afterBranchValue args live arena fits installed normal
  let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
  let ready:=Input.CallNormal.continuationEntry source built "bv" answer
  have readyArena : Rlp.Validation.Arena ready cursor limit:=nextArena.of_fields built ready cursor limit rfl rfl
  have readyAbove : Rlp.Validation.Above source ready cursor.toNat:=above
  have readyFrame : Rlp.CurrentItem.Frame source ready:=parserFrame.of_erase rfl rfl
  have readyBefore (query : BitVec 64) (earlier : query.toNat<2952790016) : ready.memory query=source.memory query:=
    readyFrame.outside query (Or.inl earlier)
  have readyView:=view.regions_frame source ready record db 2952790016 cursor.toNat data view.persistent recordAbove domain
    readyBefore (fun query higher=>readyAbove query higher)
  exact ⟨item,built,header,bytes,flag,inner,selected,valid,readyView,readyArena,readyAbove,readyFrame,domain,endian,code,globalCells,
    Input.CallNormal.continuation_lookup_same _ _ _ _,continued,endpoint⟩

/-- The actual arr2 declaration and final-value call expose their genuine
continuation and both lexical restorations, retaining physical ownership. -/
theorem branch_finish_normal (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db node heap cursor limit : BitVec 64) (data : WitnessRecord.Description)
    (index : Fin 16) (occupied : Fin 17)
    (view : WitnessRecord.View source record db data) (payload : data.payload=.branch node index occupied)
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit) (before : data.BeforeHeap heap.toNat)
    (recordAbove : cursor.toNat≤record.toNat)
    (installed : Input.OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source branchFinish=(none,post)) :
    ∃ item : Rlp.ListItem, ∃ built header bytes flag inner,
      let arrayReady:=QueryBranch.bind source "arr2" data.array
      let answer:=Rlp.Item.result (Rlp.Slices.itemPointer data.listPointer data.items 16) header bytes flag
      let ready:=Input.CallNormal.continuationEntry arrayReady built "bv" answer
      data.items[16]?=some item ∧ Rlp.Item.Valid (Rlp.Slices.itemPointer data.listPointer data.items 16) item.total.toNat answer ∧
      WitnessRecord.View ready record db data ∧ Rlp.Validation.Arena ready cursor limit ∧
      Rlp.Validation.Above source ready cursor.toNat ∧ Rlp.CurrentItem.Frame source ready ∧ ready.memaddrs=source.memaddrs ∧ ready.be=source.be ∧ ready.code=source.code ∧
      (∀ key,ready.globals.lookup key=source.globals.lookup key) ∧ ready.locals.lookup (ofString "bv")=some answer ∧
      evaluateHOLFiniteState ready afterBranchValue=(none,inner) ∧ post=restore source "arr2" (restore arrayReady "bv" inner) := by
  have read : eval source (readAt "top" 24#64)=some (.val (.word data.array)):=resolve_array_read source record db data view topCell
  rw [branch_finish_shape] at normal
  obtain ⟨arrayPost,continued,endpoint⟩:=Input.ScalarScope.declare_trace source post "arr2" (readAt "top" 24#64)
    data.array branchValueCall none read normal
  let arrayReady:=QueryBranch.bind source "arr2" data.array
  have arrayView:=view.of_fields source arrayReady record db data rfl rfl
  have arrayArena:=arena.of_fields source arrayReady cursor limit rfl rfl
  obtain ⟨item,built,header,bytes,flag,inner,selected,valid,readyView,readyArena,above,frame,domain,endian,code,globals,bvCell,run,restored⟩:=
    branch_value_call_normal arrayReady arrayPost record db node heap cursor limit data index occupied arrayView payload
      (bind_lookup_same _ _ _) (live.of_frame rfl) arrayArena before recordAbove installed continued
  exact ⟨item,built,header,bytes,flag,inner,selected,valid,readyView,readyArena,above,frame.of_erase rfl rfl,domain,endian,code,globals,bvCell,run,by rw [endpoint,restored]⟩

end InitECandidate.Solver.Mpt.WitnessCore

#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_value_call_normal
#print axioms InitECandidate.Solver.Mpt.WitnessCore.branch_finish_normal
