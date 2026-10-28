import InitECandidate.Solver.Headers.CurrentFieldCost

namespace InitECandidate.Solver.Headers.CurrentField
open Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix.QueryBranch

/-- Actual normal uint/bytes/raw field helpers retain every nonlocal field.
The frame follows the real item return and the literal readonly guard tail. -/
theorem body_frame (source post : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (value : ValueHOL 64) (normal : evaluateHOLFiniteState source kind.body=(some (.returned value),post)) :
    LocalEffects.erase post=LocalEffects.erase source := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩:=Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length (Rlp.Item.original_code source.code arena.code)
  rw [Field.body_shape] at normal
  obtain ⟨funded,itemPost,answer,inner,bodyRun,checked,continuation,endpoint⟩:=CallNormal.scoped_normal source post "it" Rlp.Item.resultShape (ofString "rlp_item") arguments (Rlp.Header.values pointer length) Rlp.Item.body kind.afterItem callee Rlp.Item.resultShape args called value normal
  obtain ⟨valid,frame,price⟩:=Rlp.CurrentItem.body_normal (callEntryStateHOLFinite source callee) itemPost pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits arena.code answer bodyRun
  have codeEq:=congrArg PanSemStateFiniteExact.code frame
  have tailFrame:=after_item_readonly source.code kind (CallNormal.continuationEntry source itemPost "it" answer) codeEq
  rw [continuation] at tailFrame
  rw [endpoint]
  exact tailFrame.trans frame

end InitECandidate.Solver.Headers.CurrentField

#print axioms InitECandidate.Solver.Headers.CurrentField.body_frame
