import InitECandidate.Solver.Input.FlatScalar

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- A generated flattened uint32 expression reads its actual copied input field. -/
theorem flat_heap_le32 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer basePointer : BitVec 64) (base : ExpHOL 64) (extras : List Nat) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+4≤input.length%2^64)
    (baseRead : eval source base=some (.val (.word basePointer)))
    (field : basePointer+BitVec.ofNat 64 extras.sum=pointer+BitVec.ofNat 64 start) :
    eval source (flat32 base extras)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le32 input start)))) := by
  have addressRead:=flat_read source base basePointer extras baseRead
  rw [field] at addressRead
  exact (flat32_equiv source base basePointer extras baseRead).trans
    (heap_le32 source input pointer start _ heap inside addressRead)

/-- The same copied-input connection for the generated uint64 expression. -/
theorem flat_heap_le64 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer basePointer : BitVec 64) (base : ExpHOL 64) (extras : List Nat) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+8≤input.length%2^64)
    (baseRead : eval source base=some (.val (.word basePointer)))
    (field : basePointer+BitVec.ofNat 64 extras.sum=pointer+BitVec.ofNat 64 start) :
    eval source (flat64 base extras)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))) := by
  have addressRead:=flat_read source base basePointer extras baseRead
  rw [field] at addressRead
  exact (flat64_equiv source base basePointer extras baseRead).trans
    (heap_le64 source input pointer start _ heap inside addressRead)

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.flat_heap_le32
#print axioms InitECandidate.Solver.Input.Scalar.flat_heap_le64
