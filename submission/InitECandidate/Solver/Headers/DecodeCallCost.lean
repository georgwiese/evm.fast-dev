import InitECandidate.Solver.Headers.DecodeCost

namespace InitECandidate.Solver.Headers.Decode
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The genuine original decode_header caller, from its actual physical
input and arena context. Assignment/ignored destinations and every outcome
are included; the caller spends at most one additional source tick. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (pointer length heap cursor limit : BitVec 64) (cutoff : Nat)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some (Rlp.Header.values pointer length))
    (arena : Rlp.Validation.Arena source cursor limit)
    (heapGlobal : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (before : pointer.toNat+length.toNat≤heap.toNat) (sizeBound : 16*length.toNat<2^64)
    (inputLower : 2701131776≤pointer.toNat) (heapAligned : heap.toNat%8=0)
    (aligned : cutoff%8=0) (scratchBelow : cursor.toNat≤cutoff) (inputAbove : cutoff≤pointer.toNat)
    (installed : Input.OriginalCode.Installed source.code) (shape : source.eshapes.lookup (ofString "HdrErr")=some .one) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "decode_header") expressions)).2.clock≤251*length.toNat+1374 := by
  obtain ⟨callee,called,pointerCell,lengthCell⟩ := Rlp.environment source.code.lookup (ofString "decode_header") body .one pointer length (original_code source.code installed)
  have entered:=Rlp.Validation.Arena.of_fields source (callEntryStateHOLFinite source callee) cursor limit arena rfl rfl
  have priced:=body_cost (callEntryStateHOLFinite source callee) pointer length heap cursor limit cutoff pointerCell lengthCell entered heapGlobal heapBound before sizeBound inputLower heapAligned aligned scratchBelow inputAbove installed shape
  exact Input.ClockCost.call_current source destination (ofString "decode_header") expressions _ body callee .one (251*length.toNat+1373) args called priced

end InitECandidate.Solver.Headers.Decode

#print axioms InitECandidate.Solver.Headers.Decode.call_cost
