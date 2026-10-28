import InitECandidate.Solver.Rlp.CurrentValidation.Cost
import InitECandidate.Solver.Rlp.Environment
import InitECandidate.Solver.Input.ClockCostCurrentCall

namespace InitECandidate.Solver.Rlp.CurrentValidation
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The genuine unchanged internal-validator ABI adds one source caller
tick. Its real initialized cursors/domain and p/len locals reach that same
callee; allocation room and future successful parsing are not premises. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length : BitVec 64)
    (arena : CurrentStartup.ArenaState source) (fits : pointer.toNat+length.toNat<2^64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length)) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "_rlp_validate_items_body") expressions)).2.clock≤14*(length.toNat+1)+1 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "_rlp_validate_items_body") Validation.body .one pointer length
    (Validation.original_code source.code arena.code)
  have nextArena : CurrentStartup.ArenaState (callEntryStateHOLFinite source callee) := arena.of_frame rfl
  have paid:=body_cost (callEntryStateHOLFinite source callee) pointer length pointerLocal lengthLocal nextArena fits
  exact ClockCost.call_current source destination (ofString "_rlp_validate_items_body") expressions (Header.values pointer length) Validation.body callee .one
    (14*(length.toNat+1)) args called paid

end InitECandidate.Solver.Rlp.CurrentValidation

#print axioms InitECandidate.Solver.Rlp.CurrentValidation.call_cost
