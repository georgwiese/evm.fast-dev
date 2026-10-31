import InitECandidate.Solver.Rlp.DecodeProgram
import InitECandidate.Solver.Rlp.CurrentItem.Cost

namespace InitECandidate.Solver.Rlp.CurrentDecode
open Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix.QueryBranch

theorem after_item_price (code) (installed : Input.OriginalCode.Installed code) : Input.ClockCost.Bound code afterItem 1 :=
  Fail.guard_price code installed _ _ _ 0 (Input.ClockCost.returned code _)

theorem body_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (pointerCell : source.locals.lookup (ofString "p")=some (.val (.word pointer)))
    (lengthCell : source.locals.lookup (ofString "len")=some (.val (.word length)))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source body).2.clock≤60*length.toNat+12 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_item") Item.body Item.resultShape pointer length (Item.original_code source.code installed)
  have args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length) := by
    simp [arguments,Header.values,evalListHOLFinite,evalListHOLExact,evalHOLExact,localVar,toExact,pointerCell,lengthCell]
  rw [body_shape]
  have price := Input.ClockCost.scoped_current source (ofString "it") Item.resultShape (ofString "rlp_item") arguments _ Item.body afterItem callee Item.resultShape (60*length.toNat+10) 1 args called
    (CurrentItem.body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits installed)
    (after_item_price source.code installed)
  omega

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : LiveArena source) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_decode_fully") expressions)).2.clock≤60*length.toNat+13 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_decode_fully") body Item.resultShape pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_decode_fully") expressions _ body callee Item.resultShape (60*length.toNat+12) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal (arena.of_frame rfl) fits installed)

end InitECandidate.Solver.Rlp.CurrentDecode

#print axioms InitECandidate.Solver.Rlp.CurrentDecode.body_cost
#print axioms InitECandidate.Solver.Rlp.CurrentDecode.call_cost
