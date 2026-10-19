import InitECandidate.Solver.Rlp.ValidationWrapper

namespace InitECandidate.Solver.Rlp.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (destination : Option (Option MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) arguments=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_validate_items") arguments)).2.clock≤14*(2*length.toNat+1)+5 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_validate_items") body .one pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_validate_items") arguments _ body callee .one (14*(2*length.toNat+1)+4) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal
      (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)

end InitECandidate.Solver.Rlp.Validate

#print axioms InitECandidate.Solver.Rlp.Validate.call_cost
