import InitECandidate.Solver.Input.CoreResolveCallNormal
import InitECandidate.Solver.Mpt.WitnessCoreResolveState
import InitECandidate.Solver.Input.ScalarScopeTrace

namespace InitECandidate.Solver.Input.Main.RunAttemptConstructors
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

/-- A whole original resolve-mode iteration that continues has the
genuine parser/table result and one of the original two concrete state
updates, including both lexical restorations. Its active record remains
owned, scratch is restored and next decode slices are bounded. -/
theorem core_resolve_normal (input : Guest.InputBlob) (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (record db heap cursor limit oldResult oldPointer oldLength oldMode : BitVec 64) (data : Mpt.WitnessRecord.Description)
    (view : Mpt.WitnessRecord.View source record db data) (boundary : RootBoundary input source)
    (dbCell : source.locals.lookup (ofString "db")=some (.val (.word db)))
    (topCell : source.locals.lookup (ofString "top")=some (.val (.word record)))
    (slotCell : source.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))))
    (resultCell : source.locals.lookup (ofString "result")=some (.val (.word oldResult)))
    (pointerCell : source.locals.lookup (ofString "cur_p")=some (.val (.word oldPointer)))
    (lengthCell : source.locals.lookup (ofString "cur_n")=some (.val (.word oldLength)))
    (modeCell : source.locals.lookup (ofString "mode")=some (.val (.word oldMode)))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (arena : Rlp.Validation.Arena source cursor limit) (below : cursor.toNat≤2713717616)
    (recordAbove : cursor.toNat≤record.toNat) (heapLower : 2713731432≤heap.toNat) (before : data.BeforeHeap heap.toNat)
    (installed : OriginalCode.Installed source.code)
    (normal : evaluateHOLFiniteState source Mpt.WitnessCore.resolveBranch=(none,post)) :
    let arrState:=QueryBranch.bind source "arr" data.array
    ∃ built returned,
      let ready:=CallNormal.continuationEntry arrState built "r" returned
      ResolveFrame source ready heap cursor limit ∧ ResolveResult ready db heap returned ∧
      Mpt.WitnessRecord.View post record db data ∧ Rlp.Validation.Arena post cursor limit ∧ post.globals=ready.globals ∧
      ((∃ node,returned=Mpt.WitnessCore.resolveAnswer 0#64 node 0#64 0#64 ∧ (node=0#64 ∨ node=heap) ∧
          post=restore source "arr" (restore arrState "r" (Mpt.WitnessCore.resolvedTerminal ready record node))) ∨
        ∃ nextPointer nextLength pending,returned=Mpt.WitnessCore.resolveAnswer 1#64 nextPointer nextLength pending ∧
          nextLength.toNat≤1024 ∧ 2713731432≤nextPointer.toNat ∧ nextPointer.toNat+nextLength.toNat≤db.toNat ∧
          (pending=0#64 ∨ 2713731432≤pending.toNat ∧ pending.toNat+32≤db.toNat) ∧
          post=restore source "arr" (restore arrState "r" (Mpt.WitnessCore.resolvedDecode ready record nextPointer nextLength pending))) := by
  let arrState:=QueryBranch.bind source "arr" data.array
  have arrayRead:=Mpt.WitnessCore.resolve_array_read source record db data view topCell
  rw [Mpt.WitnessCore.resolve_shape] at normal
  obtain ⟨callPost,callRun,arrEndpoint⟩:=ScalarScope.declare_trace source post "arr" Mpt.WitnessCore.resolveArray data.array Mpt.WitnessCore.resolveCall none arrayRead normal
  have arrBoundary:=boundary.erase_frame input source arrState rfl (bind_lookup_other source "arr" "db" _ (by decide))
  have arrView:=view.of_fields source arrState record db data rfl rfl
  have arrDb : arrState.locals.lookup (ofString "db")=some (.val (.word db)):=
    (bind_lookup_other source "arr" "db" _ (by decide)).trans dbCell
  have arrSlot : arrState.locals.lookup (ofString "slot")=some (.val (.word (BitVec.ofNat 64 data.payload.slotIndex))):=
    (bind_lookup_other source "arr" "slot" _ (by decide)).trans slotCell
  obtain ⟨built,returned,inner,callFrame,readyView,result,rCell,continued,endpoint⟩:=core_resolve_call_normal input arrState callPost record db heap cursor limit data arrView arrBoundary
    (bind_lookup_same _ _ _) arrDb arrSlot heapCell (arena.of_fields source arrState cursor limit rfl rfl) below recordAbove heapLower before installed callRun
  let ready:=CallNormal.continuationEntry arrState built "r" returned
  have frame : ResolveFrame source ready heap cursor limit:=
    callFrame.prefix source arrState ready heap cursor limit rfl rfl rfl (fun _=>rfl) (fun _ _=>rfl)
  have locals (name : String) (notArr : ofString "arr"≠ofString name) (notR : ofString "r"≠ofString name) :
      ready.locals.lookup (ofString name)=source.locals.lookup (ofString name):=
    (CallNormal.continuation_lookup_other arrState built "r" name returned notR).trans (bind_lookup_other source "arr" name data.array notArr)
  have currentTop : ready.locals.lookup (ofString "top")=some (.val (.word record)):=(locals "top" (by decide) (by decide)).trans topCell
  have currentResult : ready.locals.lookup (ofString "result")=some (.val (.word oldResult)):=(locals "result" (by decide) (by decide)).trans resultCell
  have currentPointer : ready.locals.lookup (ofString "cur_p")=some (.val (.word oldPointer)):=(locals "cur_p" (by decide) (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "cur_n")=some (.val (.word oldLength)):=(locals "cur_n" (by decide) (by decide)).trans lengthCell
  have currentMode : ready.locals.lookup (ofString "mode")=some (.val (.word oldMode)):=(locals "mode" (by decide) (by decide)).trans modeCell
  have terminal (node : BitVec 64) (valueEq : returned=Mpt.WitnessCore.resolveAnswer 0#64 node 0#64 0#64) :
      post=restore source "arr" (restore arrState "r" (Mpt.WitnessCore.resolvedTerminal ready record node)) := by
    have nodeR:=rCell.trans (congrArg some valueEq)
    have actual:=Mpt.WitnessCore.after_resolve_choice ready 0#64 node 0#64 0#64 nodeR
    rw [if_pos rfl,Mpt.WitnessCore.resolve_terminal_execute ready record db node 0#64 0#64 oldResult oldMode data readyView currentTop nodeR currentResult currentMode] at actual
    have innerEq:=congrArg Prod.snd (continued.symm.trans actual)
    change inner=Mpt.WitnessCore.resolvedTerminal ready record node at innerEq
    rw [arrEndpoint,endpoint,innerEq]
  rcases result with empty|⟨hashed,nodeArena,tag,hashData⟩|⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingSpan⟩
  · have postEq:=terminal 0#64 empty
    have postView : Mpt.WitnessRecord.View post record db data:=by
      rw [postEq]
      exact (Mpt.WitnessCore.resolved_terminal_view ready record db 0#64 data readyView).of_fields _ _ record db data rfl rfl
    have postArena : Rlp.Validation.Arena post cursor limit:=by
      apply frame.arena.of_fields ready post cursor limit
      · rw [postEq]; rfl
      · rw [postEq]; rfl
    exact ⟨built,returned,frame,Or.inl empty,postView,postArena,by rw [postEq]; rfl,Or.inl ⟨0#64,empty,Or.inl rfl,postEq⟩⟩
  · have postEq:=terminal heap hashed
    have postView : Mpt.WitnessRecord.View post record db data:=by
      rw [postEq]
      exact (Mpt.WitnessCore.resolved_terminal_view ready record db heap data readyView).of_fields _ _ record db data rfl rfl
    have postArena : Rlp.Validation.Arena post cursor limit:=by
      apply frame.arena.of_fields ready post cursor limit
      · rw [postEq]; rfl
      · rw [postEq]; rfl
    exact ⟨built,returned,frame,Or.inr (Or.inl ⟨hashed,nodeArena,tag,hashData⟩),postView,postArena,by rw [postEq]; rfl,Or.inl ⟨heap,hashed,Or.inr rfl,postEq⟩⟩
  · have sliceR:=rCell.trans (congrArg some valueEq)
    have actual:=Mpt.WitnessCore.after_resolve_choice ready 1#64 nextPointer nextLength pending sliceR
    rw [if_neg (by decide),Mpt.WitnessCore.resolve_decode_execute ready record db nextPointer nextLength pending oldPointer oldLength oldMode data readyView currentTop sliceR currentPointer currentLength currentMode] at actual
    have innerEq:=congrArg Prod.snd (continued.symm.trans actual)
    change inner=Mpt.WitnessCore.resolvedDecode ready record nextPointer nextLength pending at innerEq
    have postEq : post=restore source "arr" (restore arrState "r" (Mpt.WitnessCore.resolvedDecode ready record nextPointer nextLength pending)):=by
      rw [arrEndpoint,endpoint,innerEq]
    have postView : Mpt.WitnessRecord.View post record db data:=by
      rw [postEq]
      exact (Mpt.WitnessCore.resolved_decode_view ready record db nextPointer nextLength pending data readyView).of_fields _ _ record db data rfl rfl
    have postArena : Rlp.Validation.Arena post cursor limit:=by
      apply frame.arena.of_fields ready post cursor limit
      · rw [postEq]; rfl
      · rw [postEq]; rfl
    exact ⟨built,returned,frame,Or.inr (Or.inr ⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingSpan⟩),postView,postArena,by rw [postEq]; rfl,
      Or.inr ⟨nextPointer,nextLength,pending,valueEq,nextSmall,nextLower,nextBefore,pendingSpan,postEq⟩⟩

end InitECandidate.Solver.Input.Main.RunAttemptConstructors

#print axioms InitECandidate.Solver.Input.Main.RunAttemptConstructors.core_resolve_normal
