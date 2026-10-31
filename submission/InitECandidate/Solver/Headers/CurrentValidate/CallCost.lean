import InitECandidate.Solver.Headers.CurrentValidate.Cost
import InitECandidate.Solver.Input.WordPairEnvironment

namespace InitECandidate.Solver.Headers.CurrentValidate
open Validate
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString Input WitnessRadix

/-- The actual ordinary validator caller adds one source tick. Initial
physical rows/workspace suffice; no later allocation or comparison is assumed. -/
theorem call_cost (source : PanSemStateFiniteExact 64 Guest.HostMemory)
    (array heap count stp pad : BitVec 64) (pointers lengths : Nat→BitVec 64) (lower upper : Nat)
    (destination : Option (Option MlS)) (expressions : List (ExpHOL 64))
    (args : evalListHOLFinite source (h:=fun query=>Classical.propDecidable (source.memaddrs query)) expressions=some [.val (.word array),.val (.word count)])
    (arena : CurrentStartup.ArenaState source) (environment : CurrentKeccak.Hash.Environment source stp pad)
    (rows : Rows source array pointers lengths count.toNat lower upper)
    (heapCell : source.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapLower : 2701131776≤heap.toNat) (heapBound : heap.toNat≤2952790016) (heapAligned : heap.toNat%8=0)
    (before : upper≤heap.toNat) (stateBefore : stp.toNat+200≤lower) (padBefore : pad.toNat+136≤lower)
    (aligned : lower%8=0) (inputLower : 2701131776≤lower)
    (lengthLimits : ∀ index<count.toNat,(lengths index).toNat≤1024) :
    source.clock-(evaluateHOLFiniteState source (.call (LocalEffects.callInfo destination) (ofString "validate_headers") expressions)).2.clock≤66208387 := by
  obtain ⟨callee,called,arrayCell,countCell⟩:=word_pair_environment source.code.lookup (ofString "validate_headers") (ofString "arr") (ofString "n") body resultShape array count (by decide) (original_code source.code arena.code)
  let entry:=callEntryStateHOLFinite source callee
  have nextArena : CurrentStartup.ArenaState entry := arena.of_frame rfl
  have nextEnvironment : CurrentKeccak.Hash.Environment entry stp pad := environment.of_frame rfl
  have nextRows:=rows.of_frame source entry array pointers lengths count.toNat lower upper ⟨by intro query lower upper; rfl⟩
  have price:=body_cost entry array heap count stp pad pointers lengths lower upper nextArena nextEnvironment nextRows arrayCell countCell heapCell
    heapLower heapBound heapAligned before stateBefore padBefore aligned inputLower lengthLimits
  exact ClockCost.call_current source destination (ofString "validate_headers") expressions _ body callee resultShape 66208386 args called price

end InitECandidate.Solver.Headers.CurrentValidate

#print axioms InitECandidate.Solver.Headers.CurrentValidate.call_cost
