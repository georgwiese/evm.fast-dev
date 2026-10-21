import InitECandidate.Solver.Headers.ValidateCost
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Headers.Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString WitnessRadix

/-- Actual original validator caller, charged at the current real decoded
row byte budget. Both assigned and ignored destinations include the
original tuple-return ABI and one additional source caller tick. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count cursor limit stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper budget : Nat)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (installed : Input.OriginalCode.Installed source.code)
    (shape : source.eshapes.lookup (ofString "HdrErr")=some .one)
    (arena : Rlp.Validation.Arena source cursor limit) (environment : Keccak256.Environment source stp pad)
    (rows : Rows source array pointers lengths count.toNat lower upper)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤33806089496) (heapAligned : heap.toNat%8=0)
    (before : upper≤heap.toNat)
    (stateArena : AllocatedBytes.Arena stp 200) (stateAligned : stp.toNat%8=0)
    (padArena : AllocatedBytes.Arena pad 136) (padAligned : pad.toNat%8=0)
    (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower) (scratchBefore : cursor.toNat≤lower)
    (byteBudget : Input.VarList.sumPrefix (fun index=>(lengths index).toNat) count.toNat≤budget) :
    source.clock-(evaluateHOLFiniteState source (.call (Input.LocalEffects.callInfo destination) (ofString "validate_headers") expressions)).2.clock≤
      251*budget+1578*count.toNat+20*(budget/136)+130*(count.toNat-1)+5 := by
  obtain ⟨callee,called,arrayCell,countCell⟩ := Input.word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code installed)
  let entry:=callEntryStateHOLFinite source callee
  have nextArena:=Rlp.Validation.Arena.of_fields source entry cursor limit arena rfl rfl
  have nextEnvironment:=Keccak256.Environment.of_fields source entry stp pad environment rfl rfl rfl (by intro key other; rfl)
  have nextRows:=rows.of_frame source entry array pointers lengths count.toNat lower upper ⟨by intro query lower upper; rfl⟩
  have priced:=body_cost entry array heap count cursor limit stp pad pointers lengths lower upper budget installed shape nextArena nextEnvironment nextRows arrayCell countCell heapCell
    heapLower heapBound heapAligned before stateArena stateAligned padArena padAligned stateBefore padBefore aligned inputLower scratchBefore byteBudget
  exact Input.ClockCost.call_current source destination (ofString "validate_headers") expressions _ body callee resultShape
    (251*budget+1578*count.toNat+20*(budget/136)+130*(count.toNat-1)+4) args called priced

end InitECandidate.Solver.Headers.Validate

#print axioms InitECandidate.Solver.Headers.Validate.call_cost
