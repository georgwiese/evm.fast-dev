import InitECandidate.Solver.Input.WitnessResolveBodyNormal
import InitECandidate.Solver.Mpt.WitnessRecordIntervalFrame
import InitECandidate.Solver.Mpt.WitnessCoreResolveRows
import InitECandidate.Solver.Input.WordTripleEnvironment
import InitECandidate.Solver.Input.ScopedCallNone
import InitECandidate.Solver.Input.CallResumeLookup

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A genuine continuing core resolver call reaches its actual r-bound
continuation with a derived bounded result, preserved active record and
complete physical resolver frame. Neither a callee result nor a future
normal continuation is supplied as an entry assumption. -/
theorem core_resolve_call_normal (databaseData : CurrentTable.NodeBuild.Data) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record heap cursor limit : BitVec 64) (data : Mpt.WitnessRecord.Description)
    (view : Mpt.WitnessRecord.View source record databaseData.table data) (database : CurrentTable.NodeLookup.Database source databaseData)
    (tableBefore : (CurrentTable.New.endPointer databaseData.table databaseData.cap).toNat≤heap.toNat)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word data.array)))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word databaseData.table)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (live : Rlp.LiveArena source) (arena : Rlp.Validation.Arena source cursor limit)
    (recordAbove : cursor.toNat≤record.toNat) (before : data.BeforeHeap heap.toNat)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.resolveCall=(none,post)) :
    ∃ built returned inner,
      let ready:=CallNormal.continuationEntry source built "r" returned
      Mpt.WitnessDecode.LiveFrame source ready heap cursor limit ∧ Mpt.WitnessRecord.View ready record databaseData.table data ∧ ResolveResult ready databaseData.table heap returned ∧ Rlp.Validation.Arena ready cursor limit ∧
      ready.locals.lookup (ofString "r")=some returned ∧
      evaluateHOLFiniteState ready Mpt.WitnessCore.afterResolve=(none,inner) ∧ post=restore source "r" inner := by
  have inside : data.payload.slotIndex<data.items.length:=by rw [view.count]; exact data.payload.slot_bound
  let item:=data.items[data.payload.slotIndex]
  have selected : data.items[data.payload.slotIndex]?=some item:=by simp [item,inside]
  have args:=Mpt.WitnessCore.resolve_arguments_read source data.array data.listPointer databaseData.table data.bytes data.payload.slotIndex data.items view.rows item selected arrayCell slotCell dbCell
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup (ofString "_resolve_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .resolve) (.comb [.one,.one,.one,.one])
    databaseData.table (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex) item.total
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .resolve source.code live.code)
  rw [Mpt.WitnessCore.resolve_call_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "r" (.comb [.one,.one,.one,.one])
    (ofString "_resolve_step") Mpt.WitnessCore.resolveArguments _ (Mpt.WitnessStep.body .resolve) Mpt.WitnessCore.afterResolve callee (.comb [.one,.one,.one,.one]) args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  obtain ⟨positive,small,pointerLower,pointerUpper⟩:=view.rows.intervals _ _ selected
  have parentSmall:=view.parentBound
  have parentLower:=view.parentLower
  have parentBefore:=view.parentBeforeDb
  have payloadLower:=view.payloadLower
  have payloadUpper:=view.payloadUpper
  have entryDatabase:=database.of_frame (show LocalEffects.erase entry=LocalEffects.erase source from rfl)
  obtain ⟨bodyFrame,named,result⟩:=resolve_body_normal databaseData entry built
    (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex) item.total heap cursor limit entryDatabase tableBefore
    dbLocal pointerLocal lengthLocal heapCell heapArena heapBound heapAligned (live.of_frame rfl) entryArena
    (by omega) (by omega) (by omega) returned bodyRun
  let ready:=CallNormal.continuationEntry source built "r" returned
  have readyFrame:=Mpt.WitnessDecode.LiveFrame.of_erase entry built source ready heap cursor limit bodyFrame rfl rfl
  have readyView:=view.live_frame source ready record databaseData.table heap cursor limit data before recordAbove readyFrame
  have readyNamed:=named.of_fields built ready cursor limit rfl rfl
  have readyResult:=result.of_fields built ready databaseData.table heap returned rfl rfl
  exact ⟨built,returned,inner,readyFrame,readyView,readyResult,readyNamed,CallNormal.continuation_lookup_same _ _ _ _,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_resolve_call_normal
