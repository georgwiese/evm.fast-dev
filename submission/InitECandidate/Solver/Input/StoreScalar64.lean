import InitECandidate.Solver.Input.StoreScalar

namespace InitECandidate.Solver.Input.Scalar
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact
open WitnessRadix.QueryBranch

/-- Real flattened LD_LE64 and ordinary store with exact scalar contents and
an input-byte frame derived from natural destination separation. -/
theorem store_le64 (source : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer basePointer address : BitVec 64) (base destination : ExpHOL 64) (extras : List Nat) (start : Nat)
    (heap : Blob.HeapInput source input pointer) (inside : start+8≤input.length%2^64)
    (baseRead : eval source base=some (.val (.word basePointer)))
    (field : basePointer+BitVec.ofNat 64 extras.sum=pointer+BitVec.ofNat 64 start)
    (destinationRead : eval source destination=some (.val (.word address))) (mapped : source.memaddrs address)
    (aligned : pointer.toNat%8=0) (fits : pointer.toNat+input.length%2^64<2^64)
    (separate : address.toNat<pointer.toNat ∨ pointer.toNat+input.length%2^64≤address.toNat) :
    evaluateHOLFiniteState source (.store destination (flat64 base extras))=
      (none,{source with memory:=WitnessRadix.StoreWord.put source.memory address (BitVec.ofNat 64 (Guest.GasLimit.le64 input start))}) ∧
    Blob.HeapInput {source with memory:=WitnessRadix.StoreWord.put source.memory address (BitVec.ofNat 64 (Guest.GasLimit.le64 input start))} input pointer := by
  have addressRead:=flat_read source base basePointer extras baseRead
  rw [field] at addressRead
  have valueRead:eval source (flat64 base extras)=some (.val (.word (BitVec.ofNat 64 (Guest.GasLimit.le64 input start)))) :=
    (flat64_equiv source base basePointer extras baseRead).trans
      (heap_le64 source input pointer start _ heap inside addressRead)
  exact ⟨WitnessRadix.StoreWord.execute source destination (flat64 base extras) address _ destinationRead valueRead mapped,
    Blob.HeapInput.store_separate source input pointer address _ heap aligned fits separate⟩

end InitECandidate.Solver.Input.Scalar

#print axioms InitECandidate.Solver.Input.Scalar.store_le64
