import InitECandidate.Solver.Headers.CurrentFieldCost
import InitECandidate.Solver.Headers.FieldResultSyntax

namespace InitECandidate.Solver.Headers.CurrentField
open Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- Actual normal uint/bytes/raw field helpers retain every nonlocal field.
A real successful field rejects list-kind items, so the actual string parser and its guard tail are readonly. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length (Rlp.Item.original_code source.code arena.code)
  rw [Field.body_shape] at normal
  obtain ⟨funded,itemPost,answer,inner,bodyRun,checked,continuation,endpoint⟩:=CallNormal.scoped_normal source post "it" Rlp.Item.resultShape (ofString "rlp_item") arguments (Rlp.Header.values pointer length) Rlp.Item.body kind.afterItem callee Rlp.Item.resultShape args called value normal
  obtain ⟨valid,frame,price⟩:=Rlp.CurrentItem.body_normal (callEntryStateHOLFinite source callee) itemPost pointer length pointerLocal lengthLocal ((Rlp.LiveArena.of_startup arena).of_frame rfl) fits arena.code answer bodyRun
  obtain ⟨header,payload,flag,same,small,positive,bounded,binary,listHeader⟩ := valid
  let ready := CallNormal.continuationEntry source itemPost "it" answer
  have cell : ready.locals.lookup (ofString "it")=some (Rlp.Item.result pointer header payload flag) := by
    simp [ready,CallNormal.continuationEntry,setVarHOLFinite,HolFiniteMapExact.update,FUPDATE,same]
  obtain ⟨zero,returnValue⟩ := after_item_normal_value ready inner kind pointer header payload flag cell value continuation
  have stringKind : Rlp.CurrentItem.kindOf answer=some 0#64 := by rw [same,zero]; rfl
  have pure := Rlp.CurrentItem.body_string_frame (callEntryStateHOLFinite source callee) itemPost pointer length
    pointerLocal lengthLocal ((Rlp.LiveArena.of_startup arena).of_frame rfl) fits arena.code answer stringKind bodyRun
  have codeEq := congrArg PanSemStateFiniteExact.code pure
  have tailFrame := after_item_readonly source.code kind ready codeEq
  rw [continuation] at tailFrame
  rw [endpoint]
  exact tailFrame.trans pure

end InitECandidate.Solver.Headers.CurrentField

#print axioms InitECandidate.Solver.Headers.CurrentField.body_frame
