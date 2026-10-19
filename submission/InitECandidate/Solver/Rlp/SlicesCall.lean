import InitECandidate.Solver.Rlp.SlicesCost

namespace InitECandidate.Solver.Rlp.Slices
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "rlp_list_to_slices") expressions)).2.clock≤71*length.toNat+35 := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  exact Input.ClockCost.call_current source destination (ofString "rlp_list_to_slices") expressions _ body callee resultShape (71*length.toNat+34) args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed)

theorem scoped_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory) (pointer length cursor limit : BitVec 64)
    (name : MlS) (expressions : List (ExpHOL 64)) (continuation : ProgHOL 64) (tailPrice : Nat)
    (args : evalListHOLFinite source (h:=fun address=>Classical.propDecidable (source.memaddrs address)) expressions=some (Header.values pointer length))
    (arena : Validation.Arena source cursor limit) (fits : pointer.toNat+length.toNat<2^64)
    (installed : Input.OriginalCode.Installed source.code) (tail : Input.ClockCost.Bound source.code continuation tailPrice) :
    source.clock-(evaluateHOLFiniteState source (.decCall name resultShape (ofString "rlp_list_to_slices") expressions continuation)).2.clock≤71*length.toNat+35+tailPrice := by
  obtain ⟨callee,called,pointerLocal,lengthLocal⟩ := Rlp.environment source.code.lookup (ofString "rlp_list_to_slices") body resultShape pointer length (original_code source.code installed)
  have priced := Input.ClockCost.scoped_current source name resultShape (ofString "rlp_list_to_slices") expressions _ body continuation callee resultShape (71*length.toNat+34) tailPrice args called
    (body_cost (callEntryStateHOLFinite source callee) pointer length cursor limit pointerLocal lengthLocal (Validation.Arena.of_fields source _ cursor limit arena rfl rfl) fits installed) tail
  omega

end InitECandidate.Solver.Rlp.Slices

#print axioms InitECandidate.Solver.Rlp.Slices.call_cost
#print axioms InitECandidate.Solver.Rlp.Slices.scoped_cost
