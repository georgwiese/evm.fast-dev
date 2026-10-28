import InitECandidate.Solver.Mpt.CurrentWitnessDecodeLeafFrame
import InitECandidate.Solver.Mpt.FailGuardReturn

namespace InitECandidate.Solver.Mpt.WitnessDecode
open Input Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

/-- The actual second-item parse is readonly before its genuine leaf
allocation and stores. The entire leaf path protects the entering frontier. -/
theorem current_leaf_body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array pointer heap parentPointer parentLength nibbles nibbleLength leaf : BitVec 64)
    (bytes : Nat) (items : List Rlp.ListItem) (item : Rlp.ListItem)
    (rows : Rows source array pointer bytes items) (selected : items[1]?=some item)
    (arrayCell : source.locals.lookup (ofString "arr")=some (.val (.word array)))
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word parentPointer)))
    (lengthCell : source.locals.lookup (ofString "n")=some (.val (.word parentLength)))
    (compactCell : source.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]))
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapArena : AllocatedBytes.Arena heap 0) (heapBound : heap.toNat≤2952790016) (aligned : heap.toNat%8=0)
    (arena : CurrentStartup.ArenaState source) (value : ValueHOL 64)
    (normal : evaluateHOLFiniteState source leafBody=(some (.returned value),post)) :
    value=.rStruct [.val (.word 0#64),.val (.word heap)] ∧ PersistentNormalFrame source post heap := by
  obtain ⟨args,positive,small,lower,upper⟩:=rows.arguments source array pointer bytes 1 items item selected arrayCell
  have fits : (Rlp.Slices.itemPointer pointer items 1).toNat+item.total.toNat<2^64:=by have h:=rows.fits; omega
  rw [value_shape] at normal
  obtain ⟨answer,clock,inner,valid,forward,price,continued,endpoint⟩:=Rlp.CurrentItem.scoped_normal source post
    (Rlp.Slices.itemPointer pointer items 1) item.total arena fits "vi" (recordArguments 1) afterValue args value normal
  obtain ⟨header,payload,flag,answerEq,headerBound,itemPositive,itemBound,binary,listHeader⟩:=valid
  rw [answerEq] at continued
  let ready:=setVarHOLFinite (ofString "vi") (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 1) header payload flag) {source with clock:=clock}
  have currentPointer : ready.locals.lookup (ofString "p")=some (.val (.word parentPointer)) :=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "vi" "p" _ (by decide)).trans pointerCell
  have currentLength : ready.locals.lookup (ofString "n")=some (.val (.word parentLength)) :=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "vi" "n" _ (by decide)).trans lengthCell
  have currentCompact : ready.locals.lookup (ofString "cn")=some (.rStruct [.val (.word nibbles),.val (.word nibbleLength),.val (.word leaf)]) :=
    (CallNormal.continuation_lookup_other source {source with clock:=clock} "vi" "cn" _ (by decide)).trans compactCell
  have valueCell : ready.locals.lookup (ofString "vi")=some (Rlp.Item.result (Rlp.Slices.itemPointer pointer items 1) header payload flag) :=
    CallNormal.continuation_lookup_same source {source with clock:=clock} "vi" _
  have readyArena : CurrentStartup.ArenaState ready:=arena.of_frame rfl
  rw [after_value_shape] at continued
  have actual:=(Fail.guard_return ready inner (.cmp .notEqual (field "vi" 0) (.const 0#64)) [.const 6#64] leafAllocate value readyArena.code continued).2
  obtain ⟨valueEq,frame⟩:=current_leaf_allocate_frame ready inner parentPointer parentLength nibbles nibbleLength leaf flag
    (Rlp.Slices.itemPointer pointer items 1+header) payload (header+payload) heap currentPointer currentLength currentCompact valueCell
    heapCell heapArena heapBound aligned readyArena value actual
  exact ⟨valueEq,frame.of_erase ready inner source post heap rfl (by rw [endpoint]; rfl)⟩

end InitECandidate.Solver.Mpt.WitnessDecode

#print axioms InitECandidate.Solver.Mpt.WitnessDecode.current_leaf_body_frame
