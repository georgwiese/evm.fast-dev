import InitECandidate.Solver.Input.HeapFrame
import InitECandidate.Solver.Input.ScalarDeclaration

namespace InitECandidate.Solver.Input.Blob
open Flapjack PanSemStateFiniteExact WitnessRadix.QueryBranch

theorem HeapInput.bind (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (name : String) (word : BitVec 64) (heap : HeapInput source input pointer) :
    HeapInput (WitnessRadix.QueryBranch.bind source name word) input pointer :=
  HeapInput.of_fields source _ input pointer rfl rfl rfl heap

theorem HeapInput.restore (saved source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob) (pointer : BitVec 64)
    (name : String) (heap : HeapInput source input pointer) :
    HeapInput (WitnessRadix.QueryBranch.restore saved name source) input pointer :=
  HeapInput.of_fields source _ input pointer rfl rfl rfl heap

end InitECandidate.Solver.Input.Blob

#print axioms InitECandidate.Solver.Input.Blob.HeapInput.bind
#print axioms InitECandidate.Solver.Input.Blob.HeapInput.restore
