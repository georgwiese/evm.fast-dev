import InitECandidate.Solver.Headers.FieldTailEffects
import InitECandidate.Solver.Rlp.CurrentItem.Call

namespace InitECandidate.Solver.Headers.CurrentField
open Field
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original uint/bytes/raw field body spends only its real
item-decoding caller clock. Its selected row length is current input data. -/
theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (kind : Kind)
    (pointer length : BitVec 64)
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) arguments=some (Rlp.Header.values pointer length))
    (arena : Input.CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source kind.body).2.clock≤46*length.toNat+11 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Rlp.Item.body Rlp.Item.resultShape pointer length (Rlp.Item.original_code source.code installed)
  have entryArena : Input.CurrentStartup.ArenaState (callEntryStateHOLFinite source callee) := arena.of_frame rfl
  have price := Input.ClockCost.scoped_current source (ofString "it") Rlp.Item.resultShape (ofString "rlp_item") arguments _ Rlp.Item.body kind.afterItem callee Rlp.Item.resultShape
    (46*length.toNat+10) 0 args called
    (Rlp.CurrentItem.body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal entryArena fits installed)
    (Input.ClockCost.of_quiet source.code kind.afterItem (after_item_quiet source.code kind))
  rw [body_shape]
  exact price

end InitECandidate.Solver.Headers.CurrentField

#print axioms InitECandidate.Solver.Headers.CurrentField.body_cost
