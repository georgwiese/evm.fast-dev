import InitECandidate.Solver.Input.Witness.BodyNormalPadded

namespace InitECandidate.Solver.Input.Witness
open Flapjack Flapjack.Pancake.PanLang PanSemStateFiniteExact WitnessRadix WitnessRadix.AllocatedBytes
open Flapjack.Basis.Pure.MlString QueryBranch

/-- Witness data survives actual lexical restoration and clock changes.
Only the physical memory, globals, mapping and endian fields are used. -/
theorem Decoded.of_fields (source target : PanSemStateFiniteExact 64 Guest.HostMemory) (input : Guest.InputBlob)
    (pointer array si : BitVec 64) (start first middle last total : Nat) (value : ValueHOL 64)
    (memory : target.memory=source.memory) (globals : target.globals=source.globals)
    (domain : target.memaddrs=source.memaddrs) (endian : target.be=source.be)
    (actual : Decoded source input pointer array si start first middle last total value) :
    Decoded target input pointer array si start first middle last total value := by
  obtain ⟨codeArray,headerArray,finalCursor,returned,nodes,codes,headers,nodeSizes,codeSizes,headerCount,bytes,nodePointer,nodeCount,codePointer,codeCount,headerPointer,headerCountCell,heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩ := actual
  exact ⟨codeArray,headerArray,finalCursor,returned,
    VarList.Records.of_memory source target _ _ _ _ _ memory nodes,
    VarList.Records.of_memory source target _ _ _ _ _ memory codes,
    VarList.Records.of_memory source target _ _ _ _ _ memory headers,
    nodeSizes,codeSizes,headerCount,Blob.HeapInput.of_fields source target input pointer memory.symm domain.symm endian.symm bytes,
    by rw [memory]; exact nodePointer,by rw [memory]; exact nodeCount,
    by rw [memory]; exact codePointer,by rw [memory]; exact codeCount,
    by rw [memory]; exact headerPointer,by rw [memory]; exact headerCountCell,
    by rw [globals]; exact heapCursor,codeAddress,headerAddress,codeAligned,headerAligned,finalAddress,finalBound,finalAligned⟩

end InitECandidate.Solver.Input.Witness

#print axioms InitECandidate.Solver.Input.Witness.Decoded.of_fields
