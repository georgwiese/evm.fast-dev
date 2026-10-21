import InitECandidate.Solver.Input.WitnessResolveBodyNormal
import InitECandidate.Solver.Input.CoreResolveViewFrame
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
theorem core_resolve_call_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap cursor limit : BitVec 64) (data : Mpt.WitnessRecord.Description)
    (view : Mpt.WitnessRecord.View source record db data) (boundary : RootBoundary input source)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word data.array)))
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (recordAbove : cursor.toNat≤record.toNat) (heapLower : 2713731432≤heap.toNat) (before : data.BeforeHeap heap.toNat)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.resolveCall=(none,post)) :
    ∃ built returned inner,
      let ready:=CallNormal.continuationEntry source built "r" returned
      ResolveFrame source ready heap cursor limit ∧ Mpt.WitnessRecord.View ready record db data ∧ ResolveResult ready db heap returned ∧
      ready.locals.lookup (ofString "r")=some returned ∧
      evaluateHOLFiniteState ready Mpt.WitnessCore.afterResolve=(none,inner) ∧ post=restore source "r" inner := by
  have inside : data.payload.slotIndex<data.items.length:=by rw [view.count]; exact data.payload.slot_bound
  let item:=data.items[data.payload.slotIndex]
  have selected : data.items[data.payload.slotIndex]?=some item:=by simp [item,inside]
  have args:=Mpt.WitnessCore.resolve_arguments_read source data.array data.listPointer db data.bytes data.payload.slotIndex data.items view.rows item selected arrayCell slotCell dbCell
  obtain ⟨callee,called,dbLocal,pointerLocal,lengthLocal⟩:=word_triple_environment source.code.lookup (ofString "_resolve_step")
    (ofString "db") (ofString "p") (ofString "n") (Mpt.WitnessStep.body .resolve) (.comb [.one,.one,.one,.one])
    db (Rlp.Slices.itemPointer data.listPointer data.items data.payload.slotIndex) item.total
    (by decide) (by decide) (by decide) (Mpt.WitnessStep.original_code .resolve source.code installed)
  rw [Mpt.WitnessCore.resolve_call_shape] at normal
  obtain ⟨funded,built,returned,inner,bodyRun,checked,continued,endpoint⟩:=CallNormal.scoped_none source post "r" (.comb [.one,.one,.one,.one])
    (ofString "_resolve_step") Mpt.WitnessCore.resolveArguments _ (Mpt.WitnessStep.body .resolve) Mpt.WitnessCore.afterResolve callee (.comb [.one,.one,.one,.one]) args called normal
  let entry:=callEntryStateHOLFinite source callee
  have entryBoundary:=boundary.erase_frame input source entry rfl (dbLocal.trans dbCell.symm)
  have entryArena:=arena.of_fields source entry cursor limit rfl rfl
  obtain ⟨positive,small,pointerLower,pointerUpper⟩:=view.rows.intervals _ _ selected
  have parentSmall:=view.parentBound
  have parentLower:=view.parentLower
  have parentBefore:=view.parentBeforeDb
  have payloadLower:=view.payloadLower
  have payloadUpper:=view.payloadUpper
  obtain ⟨actualHeap,actualCell,heapArena,heapAligned,bodyFrame,result⟩:=resolve_body_normal input entry built db _ item.total cursor limit entryBoundary dbLocal pointerLocal lengthLocal
    entryArena below (by omega) (by omega) (by omega) installed returned bodyRun
  have actualEq : actualHeap=heap:=HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj (actualCell.symm.trans heapCell)))
  subst actualHeap
  let ready:=CallNormal.continuationEntry source built "r" returned
  have readyFrame : ResolveFrame source ready heap cursor limit:=
    (bodyFrame.prefix source entry built heap cursor limit rfl rfl rfl (fun _=>rfl) (fun _ _=>rfl)).of_erase source ready built heap cursor limit rfl
  have readyView:=readyFrame.record_view source ready heap cursor limit record db data view before recordAbove below heapLower
  have readyResult:=result.of_memory built ready db heap returned rfl
  exact ⟨built,returned,inner,readyFrame,readyView,readyResult,CallNormal.continuation_lookup_same _ _ _ _,continued,endpoint⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_resolve_call_normal
