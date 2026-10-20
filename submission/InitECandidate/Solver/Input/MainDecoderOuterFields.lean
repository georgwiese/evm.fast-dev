import InitECandidate.Solver.Input.MainDecoderOuter

namespace InitECandidate.Solver.Input.Main.DecoderCall
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix
open Flapjack.Basis.Pure.MlString QueryBranch

theorem outer_globals (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (outerState source input).globals = source.globals := rfl

theorem outer_context (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    InitializerAllocations.context (outerState source input) = InitializerAllocations.context source := rfl

theorem outer_bindings (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) :
    (outerState source input).locals.lookup (ofString "p") = some (.val (.word (inputPointer + 2#64))) ∧
    (outerState source input).locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 (input.length % 2^64 - 2)))) := by
  constructor
  · exact (bind_lookup_other (QueryBranch.bind source "p" (inputPointer + 2#64)) "len" "p" _ (by decide)).trans (bind_lookup_same _ _ _)
  · exact bind_lookup_same _ _ _

theorem outer_cells (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (first : Guest.GasLimit.le32 input 2 = 16) :
    (outerState source input).memory 2713715344#64 = .word 16#64 ∧
    (outerState source input).memory 2713715352#64 = .word (BitVec.ofNat 64 (Guest.GasLimit.le32 input 6)) := by
  constructor
  · simp [outerState,Header.pairState,Header.firstState,Header.firstWord,StoreWord.put,first]
  · simp [outerState,Header.pairState,Header.secondWord,StoreWord.put]

end InitECandidate.Solver.Input.Main.DecoderCall

#print axioms InitECandidate.Solver.Input.Main.DecoderCall.outer_globals
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.outer_context
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.outer_bindings
#print axioms InitECandidate.Solver.Input.Main.DecoderCall.outer_cells
